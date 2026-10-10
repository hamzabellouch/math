import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow928 : Integer.Sparse Key := [(key1346, -2), (key1781, -2), (key1842, -2), (key1330, 1), (key1346, 1), (key1560, 1), (key1660, 1), (key1781, 1), (key1818, 1), (key1340, 2), (key1775, 2), (key1840, 2), (key1303, -1), (key1340, -1), (key1398, -1), (key1458, -1), (key1775, -1), (key1791, -1), (key1316, -1), (key1337, -1), (key1546, -1), (key1655, -1), (key1772, -1), (key1813, -1), (key1296, 1), (key1337, 1), (key1391, 1), (key1455, 1), (key1772, 1), (key1788, 1)]

theorem rawRowCheck928 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form0 = rawRow928 := by decide +kernel

def row928 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, -1), (key1660, 1), (key1775, 1), (key1781, -1), (key1788, 1), (key1791, -1), (key1813, -1), (key1818, 1), (key1840, 2), (key1842, -2)]

theorem rowCheck928 : row928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow928 := by decide +kernel

theorem rowEval928 (x : Key → ℝ) : Integer.Sparse.eval row928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck928, Integer.Sparse.eval_collectBalanced, rawRowCheck928]

def rawRow929 : Integer.Sparse Key := [(key1346, -2), (key1842, -2), (key1781, -2), (key1346, 1), (key1330, 1), (key1660, 1), (key1560, 1), (key1818, 1), (key1781, 1), (key1340, 2), (key1840, 2), (key1775, 2), (key1340, -1), (key1303, -1), (key1458, -1), (key1398, -1), (key1791, -1), (key1775, -1), (key1337, -1), (key1316, -1), (key1655, -1), (key1546, -1), (key1813, -1), (key1772, -1), (key1337, 1), (key1296, 1), (key1455, 1), (key1391, 1), (key1788, 1), (key1772, 1)]

theorem rawRowCheck929 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form0 = rawRow929 := by decide +kernel

def row929 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, -1), (key1660, 1), (key1775, 1), (key1781, -1), (key1788, 1), (key1791, -1), (key1813, -1), (key1818, 1), (key1840, 2), (key1842, -2)]

theorem rowCheck929 : row929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow929 := by decide +kernel

theorem rowEval929 (x : Key → ℝ) : Integer.Sparse.eval row929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck929, Integer.Sparse.eval_collectBalanced, rawRowCheck929]

def rawRow930 : Integer.Sparse Key := [(key1781, -2), (key1346, -2), (key1842, -2), (key1560, 1), (key1781, 1), (key1330, 1), (key1818, 1), (key1346, 1), (key1660, 1), (key1775, 2), (key1340, 2), (key1840, 2), (key1398, -1), (key1775, -1), (key1303, -1), (key1791, -1), (key1340, -1), (key1458, -1), (key1546, -1), (key1772, -1), (key1316, -1), (key1813, -1), (key1337, -1), (key1655, -1), (key1391, 1), (key1772, 1), (key1296, 1), (key1788, 1), (key1337, 1), (key1455, 1)]

theorem rawRowCheck930 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form0 = rawRow930 := by decide +kernel

def row930 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, -1), (key1660, 1), (key1775, 1), (key1781, -1), (key1788, 1), (key1791, -1), (key1813, -1), (key1818, 1), (key1840, 2), (key1842, -2)]

theorem rowCheck930 : row930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow930 := by decide +kernel

theorem rowEval930 (x : Key → ℝ) : Integer.Sparse.eval row930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck930, Integer.Sparse.eval_collectBalanced, rawRowCheck930]

def rawRow931 : Integer.Sparse Key := [(key1781, -2), (key1842, -2), (key1346, -2), (key1781, 1), (key1560, 1), (key1818, 1), (key1330, 1), (key1660, 1), (key1346, 1), (key1775, 2), (key1840, 2), (key1340, 2), (key1775, -1), (key1398, -1), (key1791, -1), (key1303, -1), (key1458, -1), (key1340, -1), (key1772, -1), (key1546, -1), (key1813, -1), (key1316, -1), (key1655, -1), (key1337, -1), (key1772, 1), (key1391, 1), (key1788, 1), (key1296, 1), (key1455, 1), (key1337, 1)]

theorem rawRowCheck931 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form0 = rawRow931 := by decide +kernel

def row931 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, -1), (key1660, 1), (key1775, 1), (key1781, -1), (key1788, 1), (key1791, -1), (key1813, -1), (key1818, 1), (key1840, 2), (key1842, -2)]

theorem rowCheck931 : row931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow931 := by decide +kernel

theorem rowEval931 (x : Key → ℝ) : Integer.Sparse.eval row931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck931, Integer.Sparse.eval_collectBalanced, rawRowCheck931]

def rawRow932 : Integer.Sparse Key := [(key1842, -2), (key1346, -2), (key1781, -2), (key1660, 1), (key1818, 1), (key1346, 1), (key1781, 1), (key1330, 1), (key1560, 1), (key1840, 2), (key1340, 2), (key1775, 2), (key1458, -1), (key1791, -1), (key1340, -1), (key1775, -1), (key1303, -1), (key1398, -1), (key1655, -1), (key1813, -1), (key1337, -1), (key1772, -1), (key1316, -1), (key1546, -1), (key1455, 1), (key1788, 1), (key1337, 1), (key1772, 1), (key1296, 1), (key1391, 1)]

theorem rawRowCheck932 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form0 = rawRow932 := by decide +kernel

def row932 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, -1), (key1660, 1), (key1775, 1), (key1781, -1), (key1788, 1), (key1791, -1), (key1813, -1), (key1818, 1), (key1840, 2), (key1842, -2)]

theorem rowCheck932 : row932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow932 := by decide +kernel

theorem rowEval932 (x : Key → ℝ) : Integer.Sparse.eval row932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck932, Integer.Sparse.eval_collectBalanced, rawRowCheck932]

def rawRow933 : Integer.Sparse Key := [(key1842, -2), (key1781, -2), (key1346, -2), (key1818, 1), (key1660, 1), (key1781, 1), (key1346, 1), (key1560, 1), (key1330, 1), (key1840, 2), (key1775, 2), (key1340, 2), (key1791, -1), (key1458, -1), (key1775, -1), (key1340, -1), (key1398, -1), (key1303, -1), (key1813, -1), (key1655, -1), (key1772, -1), (key1337, -1), (key1546, -1), (key1316, -1), (key1788, 1), (key1455, 1), (key1772, 1), (key1337, 1), (key1391, 1), (key1296, 1)]

theorem rawRowCheck933 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form0 = rawRow933 := by decide +kernel

def row933 : Integer.Sparse Key := [(key1296, 1), (key1303, -1), (key1316, -1), (key1330, 1), (key1340, 1), (key1346, -1), (key1391, 1), (key1398, -1), (key1455, 1), (key1458, -1), (key1546, -1), (key1560, 1), (key1655, -1), (key1660, 1), (key1775, 1), (key1781, -1), (key1788, 1), (key1791, -1), (key1813, -1), (key1818, 1), (key1840, 2), (key1842, -2)]

theorem rowCheck933 : row933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow933 := by decide +kernel

theorem rowEval933 (x : Key → ℝ) : Integer.Sparse.eval row933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck933, Integer.Sparse.eval_collectBalanced, rawRowCheck933]

def rawRow934 : Integer.Sparse Key := [(key387, -6), (key304, 2), (key387, 2), (key396, 2), (key408, 6), (key238, -2), (key408, -2), (key417, -2), (key318, -2), (key437, -2), (key441, -2), (key250, 2), (key437, 2), (key449, 2)]

theorem rawRowCheck934 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form1 = rawRow934 := by decide +kernel

def row934 : Integer.Sparse Key := [(key238, -2), (key250, 2), (key304, 2), (key318, -2), (key387, -4), (key396, 2), (key408, 4), (key417, -2), (key441, -2), (key449, 2)]

theorem rowCheck934 : row934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow934 := by decide +kernel

theorem rowEval934 (x : Key → ℝ) : Integer.Sparse.eval row934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck934, Integer.Sparse.eval_collectBalanced, rawRowCheck934]

def rawRow935 : Integer.Sparse Key := [(key387, -6), (key304, 2), (key396, 2), (key387, 2), (key408, 6), (key238, -2), (key417, -2), (key408, -2), (key318, -2), (key441, -2), (key437, -2), (key250, 2), (key449, 2), (key437, 2)]

theorem rawRowCheck935 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form1 = rawRow935 := by decide +kernel

def row935 : Integer.Sparse Key := [(key238, -2), (key250, 2), (key304, 2), (key318, -2), (key387, -4), (key396, 2), (key408, 4), (key417, -2), (key441, -2), (key449, 2)]

theorem rowCheck935 : row935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow935 := by decide +kernel

theorem rowEval935 (x : Key → ℝ) : Integer.Sparse.eval row935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck935, Integer.Sparse.eval_collectBalanced, rawRowCheck935]

def rawRow936 : Integer.Sparse Key := [(key387, -6), (key387, 2), (key304, 2), (key396, 2), (key408, 6), (key408, -2), (key238, -2), (key417, -2), (key437, -2), (key318, -2), (key441, -2), (key437, 2), (key250, 2), (key449, 2)]

theorem rawRowCheck936 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form1 = rawRow936 := by decide +kernel

def row936 : Integer.Sparse Key := [(key238, -2), (key250, 2), (key304, 2), (key318, -2), (key387, -4), (key396, 2), (key408, 4), (key417, -2), (key441, -2), (key449, 2)]

theorem rowCheck936 : row936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow936 := by decide +kernel

theorem rowEval936 (x : Key → ℝ) : Integer.Sparse.eval row936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck936, Integer.Sparse.eval_collectBalanced, rawRowCheck936]

def rawRow937 : Integer.Sparse Key := [(key387, -6), (key387, 2), (key396, 2), (key304, 2), (key408, 6), (key408, -2), (key417, -2), (key238, -2), (key437, -2), (key441, -2), (key318, -2), (key437, 2), (key449, 2), (key250, 2)]

theorem rawRowCheck937 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form1 = rawRow937 := by decide +kernel

def row937 : Integer.Sparse Key := [(key238, -2), (key250, 2), (key304, 2), (key318, -2), (key387, -4), (key396, 2), (key408, 4), (key417, -2), (key441, -2), (key449, 2)]

theorem rowCheck937 : row937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow937 := by decide +kernel

theorem rowEval937 (x : Key → ℝ) : Integer.Sparse.eval row937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck937, Integer.Sparse.eval_collectBalanced, rawRowCheck937]

def rawRow938 : Integer.Sparse Key := [(key387, -6), (key396, 2), (key304, 2), (key387, 2), (key408, 6), (key417, -2), (key238, -2), (key408, -2), (key441, -2), (key318, -2), (key437, -2), (key449, 2), (key250, 2), (key437, 2)]

theorem rawRowCheck938 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form1 = rawRow938 := by decide +kernel

def row938 : Integer.Sparse Key := [(key238, -2), (key250, 2), (key304, 2), (key318, -2), (key387, -4), (key396, 2), (key408, 4), (key417, -2), (key441, -2), (key449, 2)]

theorem rowCheck938 : row938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow938 := by decide +kernel

theorem rowEval938 (x : Key → ℝ) : Integer.Sparse.eval row938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck938, Integer.Sparse.eval_collectBalanced, rawRowCheck938]

def rawRow939 : Integer.Sparse Key := [(key387, -6), (key396, 2), (key387, 2), (key304, 2), (key408, 6), (key417, -2), (key408, -2), (key238, -2), (key441, -2), (key437, -2), (key318, -2), (key449, 2), (key437, 2), (key250, 2)]

theorem rawRowCheck939 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form1 = rawRow939 := by decide +kernel

def row939 : Integer.Sparse Key := [(key238, -2), (key250, 2), (key304, 2), (key318, -2), (key387, -4), (key396, 2), (key408, 4), (key417, -2), (key441, -2), (key449, 2)]

theorem rowCheck939 : row939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow939 := by decide +kernel

theorem rowEval939 (x : Key → ℝ) : Integer.Sparse.eval row939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck939, Integer.Sparse.eval_collectBalanced, rawRowCheck939]

def rawRow940 : Integer.Sparse Key := [(key396, -6), (key304, 2), (key387, 2), (key387, 2), (key417, 6), (key238, -2), (key408, -2), (key408, -2), (key327, -2), (key449, -2), (key449, -2), (key259, 2), (key441, 2), (key441, 2)]

theorem rawRowCheck940 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form1 = rawRow940 := by decide +kernel

def row940 : Integer.Sparse Key := [(key238, -2), (key259, 2), (key304, 2), (key327, -2), (key387, 4), (key396, -6), (key408, -4), (key417, 6), (key441, 4), (key449, -4)]

theorem rowCheck940 : row940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow940 := by decide +kernel

theorem rowEval940 (x : Key → ℝ) : Integer.Sparse.eval row940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck940, Integer.Sparse.eval_collectBalanced, rawRowCheck940]

def rawRow941 : Integer.Sparse Key := [(key396, -6), (key387, 2), (key304, 2), (key387, 2), (key417, 6), (key408, -2), (key238, -2), (key408, -2), (key449, -2), (key327, -2), (key449, -2), (key441, 2), (key259, 2), (key441, 2)]

theorem rawRowCheck941 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form1 = rawRow941 := by decide +kernel

def row941 : Integer.Sparse Key := [(key238, -2), (key259, 2), (key304, 2), (key327, -2), (key387, 4), (key396, -6), (key408, -4), (key417, 6), (key441, 4), (key449, -4)]

theorem rowCheck941 : row941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow941 := by decide +kernel

theorem rowEval941 (x : Key → ℝ) : Integer.Sparse.eval row941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck941, Integer.Sparse.eval_collectBalanced, rawRowCheck941]

def rawRow942 : Integer.Sparse Key := [(key396, -6), (key387, 2), (key387, 2), (key304, 2), (key417, 6), (key408, -2), (key408, -2), (key238, -2), (key449, -2), (key449, -2), (key327, -2), (key441, 2), (key441, 2), (key259, 2)]

theorem rawRowCheck942 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form1 = rawRow942 := by decide +kernel

def row942 : Integer.Sparse Key := [(key238, -2), (key259, 2), (key304, 2), (key327, -2), (key387, 4), (key396, -6), (key408, -4), (key417, 6), (key441, 4), (key449, -4)]

theorem rowCheck942 : row942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow942 := by decide +kernel

theorem rowEval942 (x : Key → ℝ) : Integer.Sparse.eval row942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck942, Integer.Sparse.eval_collectBalanced, rawRowCheck942]

def rawRow943 : Integer.Sparse Key := [(key408, -6), (key318, 2), (key437, 2), (key441, 2), (key387, 6), (key250, -2), (key437, -2), (key449, -2), (key304, -2), (key387, -2), (key396, -2), (key238, 2), (key408, 2), (key417, 2)]

theorem rawRowCheck943 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form1 = rawRow943 := by decide +kernel

def row943 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, -2), (key318, 2), (key387, 4), (key396, -2), (key408, -4), (key417, 2), (key441, 2), (key449, -2)]

theorem rowCheck943 : row943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow943 := by decide +kernel

theorem rowEval943 (x : Key → ℝ) : Integer.Sparse.eval row943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck943, Integer.Sparse.eval_collectBalanced, rawRowCheck943]

def rawRow944 : Integer.Sparse Key := [(key408, -6), (key318, 2), (key441, 2), (key437, 2), (key387, 6), (key250, -2), (key449, -2), (key437, -2), (key304, -2), (key396, -2), (key387, -2), (key238, 2), (key417, 2), (key408, 2)]

theorem rawRowCheck944 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form1 = rawRow944 := by decide +kernel

def row944 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, -2), (key318, 2), (key387, 4), (key396, -2), (key408, -4), (key417, 2), (key441, 2), (key449, -2)]

theorem rowCheck944 : row944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow944 := by decide +kernel

theorem rowEval944 (x : Key → ℝ) : Integer.Sparse.eval row944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck944, Integer.Sparse.eval_collectBalanced, rawRowCheck944]

def rawRow945 : Integer.Sparse Key := [(key408, -6), (key437, 2), (key318, 2), (key441, 2), (key387, 6), (key437, -2), (key250, -2), (key449, -2), (key387, -2), (key304, -2), (key396, -2), (key408, 2), (key238, 2), (key417, 2)]

theorem rawRowCheck945 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form1 = rawRow945 := by decide +kernel

def row945 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, -2), (key318, 2), (key387, 4), (key396, -2), (key408, -4), (key417, 2), (key441, 2), (key449, -2)]

theorem rowCheck945 : row945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow945 := by decide +kernel

theorem rowEval945 (x : Key → ℝ) : Integer.Sparse.eval row945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form1) x := by
  rw [rowCheck945, Integer.Sparse.eval_collectBalanced, rawRowCheck945]

def rawRow946 : Integer.Sparse Key := [(key408, -6), (key437, 2), (key441, 2), (key318, 2), (key387, 6), (key437, -2), (key449, -2), (key250, -2), (key387, -2), (key396, -2), (key304, -2), (key408, 2), (key417, 2), (key238, 2)]

theorem rawRowCheck946 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form1 = rawRow946 := by decide +kernel

def row946 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, -2), (key318, 2), (key387, 4), (key396, -2), (key408, -4), (key417, 2), (key441, 2), (key449, -2)]

theorem rowCheck946 : row946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow946 := by decide +kernel

theorem rowEval946 (x : Key → ℝ) : Integer.Sparse.eval row946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck946, Integer.Sparse.eval_collectBalanced, rawRowCheck946]

def rawRow947 : Integer.Sparse Key := [(key408, -6), (key441, 2), (key318, 2), (key437, 2), (key387, 6), (key449, -2), (key250, -2), (key437, -2), (key396, -2), (key304, -2), (key387, -2), (key417, 2), (key238, 2), (key408, 2)]

theorem rawRowCheck947 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form1 = rawRow947 := by decide +kernel

def row947 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, -2), (key318, 2), (key387, 4), (key396, -2), (key408, -4), (key417, 2), (key441, 2), (key449, -2)]

theorem rowCheck947 : row947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow947 := by decide +kernel

theorem rowEval947 (x : Key → ℝ) : Integer.Sparse.eval row947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck947, Integer.Sparse.eval_collectBalanced, rawRowCheck947]

def rawRow948 : Integer.Sparse Key := [(key408, -6), (key441, 2), (key437, 2), (key318, 2), (key387, 6), (key449, -2), (key437, -2), (key250, -2), (key396, -2), (key387, -2), (key304, -2), (key417, 2), (key408, 2), (key238, 2)]

theorem rawRowCheck948 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form1 = rawRow948 := by decide +kernel

def row948 : Integer.Sparse Key := [(key238, 2), (key250, -2), (key304, -2), (key318, 2), (key387, 4), (key396, -2), (key408, -4), (key417, 2), (key441, 2), (key449, -2)]

theorem rowCheck948 : row948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow948 := by decide +kernel

theorem rowEval948 (x : Key → ℝ) : Integer.Sparse.eval row948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck948, Integer.Sparse.eval_collectBalanced, rawRowCheck948]

def rawRow949 : Integer.Sparse Key := [(key441, -6), (key318, 2), (key408, 2), (key437, 2), (key449, 6), (key250, -2), (key387, -2), (key437, -2), (key327, -2), (key417, -2), (key449, -2), (key259, 2), (key396, 2), (key441, 2)]

theorem rawRowCheck949 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form1 = rawRow949 := by decide +kernel

def row949 : Integer.Sparse Key := [(key250, -2), (key259, 2), (key318, 2), (key327, -2), (key387, -2), (key396, 2), (key408, 2), (key417, -2), (key441, -4), (key449, 4)]

theorem rowCheck949 : row949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow949 := by decide +kernel

theorem rowEval949 (x : Key → ℝ) : Integer.Sparse.eval row949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck949, Integer.Sparse.eval_collectBalanced, rawRowCheck949]

def rawRow950 : Integer.Sparse Key := [(key441, -6), (key318, 2), (key437, 2), (key408, 2), (key449, 6), (key250, -2), (key437, -2), (key387, -2), (key327, -2), (key449, -2), (key417, -2), (key259, 2), (key441, 2), (key396, 2)]

theorem rawRowCheck950 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form1 = rawRow950 := by decide +kernel

def row950 : Integer.Sparse Key := [(key250, -2), (key259, 2), (key318, 2), (key327, -2), (key387, -2), (key396, 2), (key408, 2), (key417, -2), (key441, -4), (key449, 4)]

theorem rowCheck950 : row950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow950 := by decide +kernel

theorem rowEval950 (x : Key → ℝ) : Integer.Sparse.eval row950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck950, Integer.Sparse.eval_collectBalanced, rawRowCheck950]

def rawRow951 : Integer.Sparse Key := [(key441, -6), (key408, 2), (key318, 2), (key437, 2), (key449, 6), (key387, -2), (key250, -2), (key437, -2), (key417, -2), (key327, -2), (key449, -2), (key396, 2), (key259, 2), (key441, 2)]

theorem rawRowCheck951 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form1 = rawRow951 := by decide +kernel

def row951 : Integer.Sparse Key := [(key250, -2), (key259, 2), (key318, 2), (key327, -2), (key387, -2), (key396, 2), (key408, 2), (key417, -2), (key441, -4), (key449, 4)]

theorem rowCheck951 : row951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow951 := by decide +kernel

theorem rowEval951 (x : Key → ℝ) : Integer.Sparse.eval row951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck951, Integer.Sparse.eval_collectBalanced, rawRowCheck951]

def rawRow952 : Integer.Sparse Key := [(key441, -6), (key408, 2), (key437, 2), (key318, 2), (key449, 6), (key387, -2), (key437, -2), (key250, -2), (key417, -2), (key449, -2), (key327, -2), (key396, 2), (key441, 2), (key259, 2)]

theorem rawRowCheck952 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form1 = rawRow952 := by decide +kernel

def row952 : Integer.Sparse Key := [(key250, -2), (key259, 2), (key318, 2), (key327, -2), (key387, -2), (key396, 2), (key408, 2), (key417, -2), (key441, -4), (key449, 4)]

theorem rowCheck952 : row952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow952 := by decide +kernel

theorem rowEval952 (x : Key → ℝ) : Integer.Sparse.eval row952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck952, Integer.Sparse.eval_collectBalanced, rawRowCheck952]

def rawRow953 : Integer.Sparse Key := [(key441, -6), (key437, 2), (key318, 2), (key408, 2), (key449, 6), (key437, -2), (key250, -2), (key387, -2), (key449, -2), (key327, -2), (key417, -2), (key441, 2), (key259, 2), (key396, 2)]

theorem rawRowCheck953 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form1 = rawRow953 := by decide +kernel

def row953 : Integer.Sparse Key := [(key250, -2), (key259, 2), (key318, 2), (key327, -2), (key387, -2), (key396, 2), (key408, 2), (key417, -2), (key441, -4), (key449, 4)]

theorem rowCheck953 : row953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow953 := by decide +kernel

theorem rowEval953 (x : Key → ℝ) : Integer.Sparse.eval row953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck953, Integer.Sparse.eval_collectBalanced, rawRowCheck953]

def rawRow954 : Integer.Sparse Key := [(key441, -6), (key437, 2), (key408, 2), (key318, 2), (key449, 6), (key437, -2), (key387, -2), (key250, -2), (key449, -2), (key417, -2), (key327, -2), (key441, 2), (key396, 2), (key259, 2)]

theorem rawRowCheck954 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form1 = rawRow954 := by decide +kernel

def row954 : Integer.Sparse Key := [(key250, -2), (key259, 2), (key318, 2), (key327, -2), (key387, -2), (key396, 2), (key408, 2), (key417, -2), (key441, -4), (key449, 4)]

theorem rowCheck954 : row954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow954 := by decide +kernel

theorem rowEval954 (x : Key → ℝ) : Integer.Sparse.eval row954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck954, Integer.Sparse.eval_collectBalanced, rawRowCheck954]

def rawRow955 : Integer.Sparse Key := [(key417, -6), (key327, 2), (key449, 2), (key449, 2), (key396, 6), (key259, -2), (key441, -2), (key441, -2), (key304, -2), (key387, -2), (key387, -2), (key238, 2), (key408, 2), (key408, 2)]

theorem rawRowCheck955 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form1 = rawRow955 := by decide +kernel

def row955 : Integer.Sparse Key := [(key238, 2), (key259, -2), (key304, -2), (key327, 2), (key387, -4), (key396, 6), (key408, 4), (key417, -6), (key441, -4), (key449, 4)]

theorem rowCheck955 : row955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow955 := by decide +kernel

theorem rowEval955 (x : Key → ℝ) : Integer.Sparse.eval row955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck955, Integer.Sparse.eval_collectBalanced, rawRowCheck955]

def rawRow956 : Integer.Sparse Key := [(key417, -6), (key449, 2), (key327, 2), (key449, 2), (key396, 6), (key441, -2), (key259, -2), (key441, -2), (key387, -2), (key304, -2), (key387, -2), (key408, 2), (key238, 2), (key408, 2)]

theorem rawRowCheck956 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form1 = rawRow956 := by decide +kernel

def row956 : Integer.Sparse Key := [(key238, 2), (key259, -2), (key304, -2), (key327, 2), (key387, -4), (key396, 6), (key408, 4), (key417, -6), (key441, -4), (key449, 4)]

theorem rowCheck956 : row956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow956 := by decide +kernel

theorem rowEval956 (x : Key → ℝ) : Integer.Sparse.eval row956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck956, Integer.Sparse.eval_collectBalanced, rawRowCheck956]

def rawRow957 : Integer.Sparse Key := [(key417, -6), (key449, 2), (key449, 2), (key327, 2), (key396, 6), (key441, -2), (key441, -2), (key259, -2), (key387, -2), (key387, -2), (key304, -2), (key408, 2), (key408, 2), (key238, 2)]

theorem rawRowCheck957 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form1 = rawRow957 := by decide +kernel

def row957 : Integer.Sparse Key := [(key238, 2), (key259, -2), (key304, -2), (key327, 2), (key387, -4), (key396, 6), (key408, 4), (key417, -6), (key441, -4), (key449, 4)]

theorem rowCheck957 : row957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow957 := by decide +kernel

theorem rowEval957 (x : Key → ℝ) : Integer.Sparse.eval row957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck957, Integer.Sparse.eval_collectBalanced, rawRowCheck957]

def rawRow958 : Integer.Sparse Key := [(key449, -6), (key327, 2), (key417, 2), (key449, 2), (key441, 6), (key259, -2), (key396, -2), (key441, -2), (key318, -2), (key408, -2), (key437, -2), (key250, 2), (key387, 2), (key437, 2)]

theorem rawRowCheck958 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form1 = rawRow958 := by decide +kernel

def row958 : Integer.Sparse Key := [(key250, 2), (key259, -2), (key318, -2), (key327, 2), (key387, 2), (key396, -2), (key408, -2), (key417, 2), (key441, 4), (key449, -4)]

theorem rowCheck958 : row958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow958 := by decide +kernel

theorem rowEval958 (x : Key → ℝ) : Integer.Sparse.eval row958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck958, Integer.Sparse.eval_collectBalanced, rawRowCheck958]

def rawRow959 : Integer.Sparse Key := [(key449, -6), (key327, 2), (key449, 2), (key417, 2), (key441, 6), (key259, -2), (key441, -2), (key396, -2), (key318, -2), (key437, -2), (key408, -2), (key250, 2), (key437, 2), (key387, 2)]

theorem rawRowCheck959 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form1 = rawRow959 := by decide +kernel

def row959 : Integer.Sparse Key := [(key250, 2), (key259, -2), (key318, -2), (key327, 2), (key387, 2), (key396, -2), (key408, -2), (key417, 2), (key441, 4), (key449, -4)]

theorem rowCheck959 : row959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow959 := by decide +kernel

theorem rowEval959 (x : Key → ℝ) : Integer.Sparse.eval row959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck959, Integer.Sparse.eval_collectBalanced, rawRowCheck959]

end MUB6.Certificate.GramRows

end OAI
