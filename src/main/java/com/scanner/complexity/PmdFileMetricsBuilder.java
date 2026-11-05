package com.scanner.complexity;

import com.github.javaparser.ParserConfiguration;
import com.scanner.complexity.AnalysisReport.ClassMetric;
import com.scanner.complexity.AnalysisReport.FileMetric;
import com.scanner.complexity.AnalysisReport.PmdViolationRow;
import com.scanner.complexity.RiskCalculator.Assessment;
import net.sourceforge.pmd.lang.java.ast.ASTCompilationUnit;
import net.sourceforge.pmd.lang.java.ast.ASTConstructorDeclaration;
import net.sourceforge.pmd.lang.java.ast.ASTExecutableDeclaration;
import net.sourceforge.pmd.lang.java.ast.ASTMethodDeclaration;
import net.sourceforge.pmd.lang.java.ast.ASTTypeDeclaration;
import net.sourceforge.pmd.lang.java.metrics.JavaMetrics;
import net.sourceforge.pmd.lang.metrics.Metric;
import net.sourceforge.pmd.lang.metrics.MetricOptions;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/** PMD AST + JavaMetrics ile metod katalogu ve risk (JavaParser kullanılmaz). */
final class PmdFileMetricsBuilder {

    private PmdFileMetricsBuilder() {
    }

    static FileMetric build(String relativePath, String sourceText,
                            ParserConfiguration.LanguageLevel languageLevel,
                            List<PmdViolationRow> fileViolations, RiskCalculator riskCalculator,
                            boolean attachDuplicateHashes) {
        return build(relativePath, sourceText, languageLevel, fileViolations, riskCalculator, attachDuplicateHashes,
                Map.of(), "");
    }

    static FileMetric build(String relativePath, String sourceText,
                            ParserConfiguration.LanguageLevel languageLevel,
                            List<PmdViolationRow> fileViolations, RiskCalculator riskCalculator,
                            boolean attachDuplicateHashes, Map<String, MethodMetric> previousMethods,
                            String fileHash) {
        return PmdMetricsAligner.withParseSession(languageLevel, session -> {
            try {
                ASTCompilationUnit unit = session.parse(sourceText, relativePath);
                return buildFromUnit(relativePath, sourceText, unit, fileViolations, riskCalculator,
                        attachDuplicateHashes, previousMethods, fileHash);
            } catch (Exception e) {
                throw new RuntimeException(relativePath + ": " + e.getMessage(), e);
            }
        });
    }

    private static FileMetric buildFromUnit(String relativePath, String sourceText, ASTCompilationUnit unit,
                                            List<PmdViolationRow> fileViolations,
                                            RiskCalculator riskCalculator, boolean attachDuplicateHashes,
                                            Map<String, MethodMetric> previousMethods, String fileHash) {
        String packageName = unit.getPackageName() == null ? "" : unit.getPackageName();
        MetricOptions options = MetricOptions.emptyOptions();
        List<ClassMetric> classes = new ArrayList<>();
        Map<String, MethodMetric> previous = previousMethods == null ? Map.of() : previousMethods;
        for (ASTTypeDeclaration type : unit.getTypeDeclarations().toList()) {
            classes.add(buildType(type, sourceText, fileViolations, options, riskCalculator, attachDuplicateHashes,
                    previous));
        }
        List<MethodMetric> allMethods = classes.stream().flatMap(c -> c.methods().stream()).toList();
        int wmc = allMethods.stream().mapToInt(MethodMetric::cyclomaticComplexity).sum();
        int maxCc = allMethods.stream().mapToInt(MethodMetric::cyclomaticComplexity).max().orElse(0);
        int loc = allMethods.stream().mapToInt(MethodMetric::codeLines).sum();
        Assessment risk = riskCalculator.assessAggregate(allMethods, loc, wmc, RiskCalculator.Scope.FILE);
        int methodsReused = (int) allMethods.stream().filter(MethodMetric::analysisReused).count();
        String resolvedFileHash = fileHash == null ? "" : fileHash;
        return new FileMetric(relativePath, packageName, unit.getEndLine(), loc, classes.size(), allMethods.size(),
                wmc, maxCc, risk.score(), risk.level(), risk.factors(), classes,
                HalsteadMetrics.EMPTY, 0, 0, 0, 0, 0, resolvedFileHash, false, methodsReused);
    }

    private static ClassMetric buildType(ASTTypeDeclaration type, String sourceText, List<PmdViolationRow> fileViolations,
                                         MetricOptions options, RiskCalculator riskCalculator,
                                         boolean attachDuplicateHashes, Map<String, MethodMetric> previousMethods) {
        String simpleName = type.getSimpleName();
        List<MethodMetric> methods = new ArrayList<>();
        String className = simpleName;
        for (ASTExecutableDeclaration exec : type.getOperations().toList()) {
            methods.add(buildMethod(exec, sourceText, fileViolations, options, riskCalculator, attachDuplicateHashes,
                    className, previousMethods));
        }
        int wmc = methods.stream().mapToInt(MethodMetric::cyclomaticComplexity).sum();
        int maxCc = methods.stream().mapToInt(MethodMetric::cyclomaticComplexity).max().orElse(0);
        double avg = methods.isEmpty() ? 0.0 : Math.round(wmc * 100.0 / methods.size()) / 100.0;
        int loc = methods.stream().mapToInt(MethodMetric::codeLines).sum();
        Assessment classRisk = riskCalculator.assessClassAggregate(methods, loc, wmc, 0, 0);
        boolean godClass = methods.stream().anyMatch(MethodMetric::godMethod)
                || fileViolations != null && fileViolations.stream()
                .anyMatch(v -> "GodClass".equals(v.ruleName()) && v.beginLine() >= type.getBeginLine()
                        && v.beginLine() <= type.getEndLine());
        return new ClassMetric(simpleName, typeKind(type), type.getBeginLine(), type.getEndLine(), methods.size(), 0,
                loc, 0, wmc, maxCc, avg, classRisk.score(), classRisk.level(), classRisk.factors(), methods,
                HalsteadMetrics.EMPTY, List.of(), 0.0, godClass, 0, 0, 0, 0, 0);
    }

    private static MethodMetric buildMethod(ASTExecutableDeclaration exec, String sourceText,
                                            List<PmdViolationRow> fileViolations, MetricOptions options,
                                            RiskCalculator riskCalculator, boolean attachDuplicateHashes,
                                            String className, Map<String, MethodMetric> previousMethods) {
        int cyclo = Metric.compute(JavaMetrics.CYCLO, exec, options);
        int cognitive = Metric.compute(JavaMetrics.COGNITIVE_COMPLEXITY, exec, options);
        int ncss = Metric.compute(JavaMetrics.NCSS, exec, options);
        int npath = PmdMetricsAligner.capNpath(Metric.compute(JavaMetrics.NPATH, exec, options));
        PmdAstMethodStats.Stats stats = PmdAstMethodStats.analyze(exec);
        HalsteadMetrics halstead = PmdHalsteadApproximation.analyze(exec);
        String name = exec.getName();
        String kind = exec instanceof ASTConstructorDeclaration ? "CONSTRUCTOR" : "METHOD";
        int arity = exec.getArity();
        String signature = name + "(" + arity + " param)";
        int start = exec.getBeginLine();
        int end = resolveMethodEndLine(sourceText, start, exec.getEndLine());
        int physical = Math.max(0, end - start + 1);
        // Risk LOC = NCSS (yorum / boş satır hariç). physical satır aralığı yorumları da kapsar — skora girmez.
        int codeLines = ncss > 0 ? ncss : Math.max(countCodeLinesExcludingComments(sourceText, start, end), 1);

        MethodMetric skeleton = MethodMetric.withoutLegacyExtensions(
                name, kind, signature, returnType(exec), start, end,
                cyclo, physical, codeLines, stats.logicalStatements(), cognitive, stats.exitPoints(),
                stats.catchClauses(), stats.switchCases(), 0, stats.lambdaCount(), stats.maxTryNestingDepth(),
                stats.localVariableCount(), 0, stats.emptyCatchBlocks(), stats.catchExceptionOrThrowable(), 0,
                0, stats.maxBooleanOperatorsInCondition(), stats.maxNestingDepth(), arity,
                false, 0.0, RiskLevel.LOW, List.of(), null, "", "", npath, ncss);

        MethodScanValues scan = MethodScanValues.withLegacyExtensions(
                baseScanFromSkeleton(skeleton), halstead, List.of(), List.of());
        scan = PmdViolationMethodEnricher.applyScanValues(scan, fileViolations, start, end);
        Assessment risk = riskCalculator.assessMethod(scan);
        boolean god = riskCalculator.isGodMethod(scan);

        PmdSourceMethodHashes.Hashes hashes = PmdSourceMethodHashes.fromSourceSlice(sourceText, start, end);
        // Cache katman 2: methodHash === bodyHash (gövde). structuralHash yalnız benzerlik.
        String bodyHash = hashes.bodyHash() == null ? "" : hashes.bodyHash();
        String methodHash = bodyHash;
        String structuralOut = attachDuplicateHashes ? hashes.structuralHash() : "";

        String cacheKey = className + "#" + signature;
        MethodMetric previous = previousMethods.get(cacheKey);
        String previousBody = previous == null ? ""
                : (previous.methodHash() != null && !previous.methodHash().isEmpty()
                ? previous.methodHash()
                : previous.bodyHash() == null ? "" : previous.bodyHash());
        boolean reuse = previous != null && !bodyHash.isEmpty() && bodyHash.equals(previousBody);
        if (reuse) {
            risk = new Assessment(previous.riskScore(), previous.riskLevel(), previous.riskFactors(),
                    previous.riskBreakdown());
            god = previous.godMethod();
        }

        return new MethodMetric(name, kind, signature, returnType(exec), start, end, cyclo, physical, codeLines,
                scan.logicalStatements(), cognitive, scan.exitPoints(), scan.catchClauses(), scan.switchCases(),
                scan.outboundDistinctCalls(), scan.lambdaCount(), scan.maxTryNestingDepth(), scan.localVariableCount(),
                scan.maxMethodCallChainLength(), scan.emptyCatchBlocks(), scan.catchExceptionOrThrowable(),
                scan.catchWithOnlyPrintStackTrace(), scan.primitiveObsessionIndex(),
                scan.maxBooleanOperatorsInCondition(), scan.maxNestingDepth(), arity, god, risk.score(), risk.level(),
                risk.factors(), risk.breakdown(), halstead, List.of(), List.of(), methodHash, reuse, List.of(),
                bodyHash, structuralOut, npath, ncss);
    }

    private static MethodScanValues baseScanFromSkeleton(MethodMetric method) {
        return new MethodScanValues(method.cyclomaticComplexity(), method.codeLines(), method.maxNestingDepth(),
                method.parameterCount(), method.cognitiveComplexity(), method.logicalStatements(), method.exitPoints(),
                method.catchClauses(), method.switchCases(), method.outboundDistinctCalls(), method.lambdaCount(),
                method.maxTryNestingDepth(), method.localVariableCount(), method.maxMethodCallChainLength(),
                method.emptyCatchBlocks(), method.catchExceptionOrThrowable(), method.catchWithOnlyPrintStackTrace(),
                method.primitiveObsessionIndex(), method.maxBooleanOperatorsInCondition(), 0, 0, 0, 0, 0, 0, 0);
    }

    /**
     * PMD {@link ASTExecutableDeclaration#getEndLine()} often equals {@code beginLine} (signature only).
     * Brace-match from {@code startLine} so JSON/DB {@code endLine} and duplicate hashes match the body.
     */
    static int resolveMethodEndLine(String sourceText, int startLine, int pmdEndLine) {
        if (pmdEndLine > startLine) {
            return pmdEndLine;
        }
        if (sourceText == null || sourceText.isEmpty() || startLine < 1) {
            return Math.max(startLine, pmdEndLine);
        }
        String[] lines = sourceText.split("\n", -1);
        if (startLine > lines.length) {
            return startLine;
        }
        int depth = 0;
        boolean bodyStarted = false;
        for (int i = startLine - 1; i < lines.length; i++) {
            String line = lines[i];
            boolean inString = false;
            char stringQuote = 0;
            for (int j = 0; j < line.length(); j++) {
                char ch = line.charAt(j);
                if (inString) {
                    if (ch == '\\') {
                        j++;
                        continue;
                    }
                    if (ch == stringQuote) {
                        inString = false;
                    }
                    continue;
                }
                if (ch == '"' || ch == '\'') {
                    inString = true;
                    stringQuote = ch;
                    continue;
                }
                if (ch == '{') {
                    depth++;
                    bodyStarted = true;
                } else if (ch == '}' && bodyStarted) {
                    depth--;
                    if (depth == 0) {
                        return i + 1;
                    }
                }
            }
        }
        for (int i = lines.length - 1; i >= startLine - 1; i--) {
            if (!lines[i].trim().isEmpty()) {
                return i + 1;
            }
        }
        return startLine;
    }

    /** Yorum ve boş satırları sayma — NCSS yoksa LOC yedek. */
    static int countCodeLinesExcludingComments(String source, int startLine, int endLine) {
        if (source == null || source.isEmpty() || startLine < 1 || endLine < startLine) {
            return 0;
        }
        String[] lines = source.split("\n", -1);
        int from = Math.min(startLine - 1, lines.length);
        int to = Math.min(endLine, lines.length);
        boolean inBlock = false;
        int count = 0;
        for (int i = from; i < to; i++) {
            String line = lines[i];
            StringBuilder code = new StringBuilder();
            for (int c = 0; c < line.length(); c++) {
                char ch = line.charAt(c);
                char next = c + 1 < line.length() ? line.charAt(c + 1) : '\0';
                if (inBlock) {
                    if (ch == '*' && next == '/') {
                        inBlock = false;
                        c++;
                    }
                    continue;
                }
                if (ch == '/' && next == '*') {
                    inBlock = true;
                    c++;
                    continue;
                }
                if (ch == '/' && next == '/') {
                    break;
                }
                code.append(ch);
            }
            if (!code.toString().trim().isEmpty()) {
                count++;
            }
        }
        return count;
    }

    private static String returnType(ASTExecutableDeclaration exec) {
        if (exec instanceof ASTMethodDeclaration method) {
            if (method.isVoid()) {
                return "void";
            }
            return method.getResultTypeNode().getTypeMirror().toString();
        }
        return "";
    }

    private static String typeKind(ASTTypeDeclaration type) {
        return switch (type.getXPathNodeName()) {
            case "InterfaceDeclaration" -> "INTERFACE";
            case "EnumDeclaration" -> "ENUM";
            case "RecordDeclaration" -> "RECORD";
            case "AnnotationTypeDeclaration" -> "ANNOTATION";
            default -> "CLASS";
        };
    }
}
