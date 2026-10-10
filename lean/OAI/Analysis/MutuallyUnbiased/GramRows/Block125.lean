import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow12928 : Integer.Sparse Key := [(key1720, -6), (key1726, -6), (key1726, -6), (key1494, -6), (key1720, 6), (key1744, 6), (key1744, 6), (key1368, 6)]

theorem rawRowCheck12928 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form16 = rawRow12928 := by decide +kernel

def row12928 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

theorem rowCheck12928 : row12928 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12928 := by decide +kernel

theorem rowEval12928 (x : Key → ℝ) : Integer.Sparse.eval row12928 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12928, Integer.Sparse.eval_collectBalanced, rawRowCheck12928]

def rawRow12929 : Integer.Sparse Key := [(key1726, -6), (key1494, -6), (key1720, -6), (key1726, -6), (key1744, 6), (key1368, 6), (key1720, 6), (key1744, 6)]

theorem rawRowCheck12929 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form16 = rawRow12929 := by decide +kernel

def row12929 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

theorem rowCheck12929 : row12929 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12929 := by decide +kernel

theorem rowEval12929 (x : Key → ℝ) : Integer.Sparse.eval row12929 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12929, Integer.Sparse.eval_collectBalanced, rawRowCheck12929]

def rawRow12930 : Integer.Sparse Key := [(key1726, -6), (key1494, -6), (key1726, -6), (key1720, -6), (key1744, 6), (key1368, 6), (key1744, 6), (key1720, 6)]

theorem rawRowCheck12930 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form16 = rawRow12930 := by decide +kernel

def row12930 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

theorem rowCheck12930 : row12930 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12930 := by decide +kernel

theorem rowEval12930 (x : Key → ℝ) : Integer.Sparse.eval row12930 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12930, Integer.Sparse.eval_collectBalanced, rawRowCheck12930]

def rawRow12931 : Integer.Sparse Key := [(key1726, -6), (key1720, -6), (key1494, -6), (key1726, -6), (key1744, 6), (key1720, 6), (key1368, 6), (key1744, 6)]

theorem rawRowCheck12931 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form16 = rawRow12931 := by decide +kernel

def row12931 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

theorem rowCheck12931 : row12931 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12931 := by decide +kernel

theorem rowEval12931 (x : Key → ℝ) : Integer.Sparse.eval row12931 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12931, Integer.Sparse.eval_collectBalanced, rawRowCheck12931]

def rawRow12932 : Integer.Sparse Key := [(key1726, -6), (key1720, -6), (key1726, -6), (key1494, -6), (key1744, 6), (key1720, 6), (key1744, 6), (key1368, 6)]

theorem rawRowCheck12932 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form16 = rawRow12932 := by decide +kernel

def row12932 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

theorem rowCheck12932 : row12932 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12932 := by decide +kernel

theorem rowEval12932 (x : Key → ℝ) : Integer.Sparse.eval row12932 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12932, Integer.Sparse.eval_collectBalanced, rawRowCheck12932]

def rawRow12933 : Integer.Sparse Key := [(key1726, -6), (key1726, -6), (key1494, -6), (key1720, -6), (key1744, 6), (key1744, 6), (key1368, 6), (key1720, 6)]

theorem rawRowCheck12933 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form16 = rawRow12933 := by decide +kernel

def row12933 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

theorem rowCheck12933 : row12933 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12933 := by decide +kernel

theorem rowEval12933 (x : Key → ℝ) : Integer.Sparse.eval row12933 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12933, Integer.Sparse.eval_collectBalanced, rawRowCheck12933]

def rawRow12934 : Integer.Sparse Key := [(key1726, -6), (key1726, -6), (key1720, -6), (key1494, -6), (key1744, 6), (key1744, 6), (key1720, 6), (key1368, 6)]

theorem rawRowCheck12934 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form16 = rawRow12934 := by decide +kernel

def row12934 : Integer.Sparse Key := [(key1368, 6), (key1494, -6), (key1726, -12), (key1744, 12)]

theorem rowCheck12934 : row12934 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12934 := by decide +kernel

theorem rowEval12934 (x : Key → ℝ) : Integer.Sparse.eval row12934 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12934, Integer.Sparse.eval_collectBalanced, rawRowCheck12934]

def rawRow12935 : Integer.Sparse Key := [(key1516, -6), (key1744, -6), (key1744, -6), (key1755, -6), (key1377, 6), (key1726, 6), (key1726, 6), (key1755, 6)]

theorem rawRowCheck12935 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form16 = rawRow12935 := by decide +kernel

def row12935 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

theorem rowCheck12935 : row12935 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12935 := by decide +kernel

theorem rowEval12935 (x : Key → ℝ) : Integer.Sparse.eval row12935 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12935, Integer.Sparse.eval_collectBalanced, rawRowCheck12935]

def rawRow12936 : Integer.Sparse Key := [(key1516, -6), (key1744, -6), (key1755, -6), (key1744, -6), (key1377, 6), (key1726, 6), (key1755, 6), (key1726, 6)]

theorem rawRowCheck12936 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form16 = rawRow12936 := by decide +kernel

def row12936 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

theorem rowCheck12936 : row12936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12936 := by decide +kernel

theorem rowEval12936 (x : Key → ℝ) : Integer.Sparse.eval row12936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12936, Integer.Sparse.eval_collectBalanced, rawRowCheck12936]

def rawRow12937 : Integer.Sparse Key := [(key1516, -6), (key1755, -6), (key1744, -6), (key1744, -6), (key1377, 6), (key1755, 6), (key1726, 6), (key1726, 6)]

theorem rawRowCheck12937 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form16 = rawRow12937 := by decide +kernel

def row12937 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

theorem rowCheck12937 : row12937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12937 := by decide +kernel

theorem rowEval12937 (x : Key → ℝ) : Integer.Sparse.eval row12937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12937, Integer.Sparse.eval_collectBalanced, rawRowCheck12937]

def rawRow12938 : Integer.Sparse Key := [(key1744, -6), (key1516, -6), (key1744, -6), (key1755, -6), (key1726, 6), (key1377, 6), (key1726, 6), (key1755, 6)]

theorem rawRowCheck12938 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form16 = rawRow12938 := by decide +kernel

def row12938 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

theorem rowCheck12938 : row12938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12938 := by decide +kernel

theorem rowEval12938 (x : Key → ℝ) : Integer.Sparse.eval row12938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12938, Integer.Sparse.eval_collectBalanced, rawRowCheck12938]

def rawRow12939 : Integer.Sparse Key := [(key1744, -6), (key1516, -6), (key1755, -6), (key1744, -6), (key1726, 6), (key1377, 6), (key1755, 6), (key1726, 6)]

theorem rawRowCheck12939 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form16 = rawRow12939 := by decide +kernel

def row12939 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

theorem rowCheck12939 : row12939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12939 := by decide +kernel

theorem rowEval12939 (x : Key → ℝ) : Integer.Sparse.eval row12939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12939, Integer.Sparse.eval_collectBalanced, rawRowCheck12939]

def rawRow12940 : Integer.Sparse Key := [(key1744, -6), (key1744, -6), (key1516, -6), (key1755, -6), (key1726, 6), (key1726, 6), (key1377, 6), (key1755, 6)]

theorem rawRowCheck12940 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form16 = rawRow12940 := by decide +kernel

def row12940 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

theorem rowCheck12940 : row12940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12940 := by decide +kernel

theorem rowEval12940 (x : Key → ℝ) : Integer.Sparse.eval row12940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form16) x := by
  rw [rowCheck12940, Integer.Sparse.eval_collectBalanced, rawRowCheck12940]

def rawRow12941 : Integer.Sparse Key := [(key1744, -6), (key1744, -6), (key1755, -6), (key1516, -6), (key1726, 6), (key1726, 6), (key1755, 6), (key1377, 6)]

theorem rawRowCheck12941 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form16 = rawRow12941 := by decide +kernel

def row12941 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

theorem rowCheck12941 : row12941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12941 := by decide +kernel

theorem rowEval12941 (x : Key → ℝ) : Integer.Sparse.eval row12941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12941, Integer.Sparse.eval_collectBalanced, rawRowCheck12941]

def rawRow12942 : Integer.Sparse Key := [(key1744, -6), (key1755, -6), (key1516, -6), (key1744, -6), (key1726, 6), (key1755, 6), (key1377, 6), (key1726, 6)]

theorem rawRowCheck12942 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form16 = rawRow12942 := by decide +kernel

def row12942 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

theorem rowCheck12942 : row12942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12942 := by decide +kernel

theorem rowEval12942 (x : Key → ℝ) : Integer.Sparse.eval row12942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12942, Integer.Sparse.eval_collectBalanced, rawRowCheck12942]

def rawRow12943 : Integer.Sparse Key := [(key1744, -6), (key1755, -6), (key1744, -6), (key1516, -6), (key1726, 6), (key1755, 6), (key1726, 6), (key1377, 6)]

theorem rawRowCheck12943 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form16 = rawRow12943 := by decide +kernel

def row12943 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

theorem rowCheck12943 : row12943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12943 := by decide +kernel

theorem rowEval12943 (x : Key → ℝ) : Integer.Sparse.eval row12943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12943, Integer.Sparse.eval_collectBalanced, rawRowCheck12943]

def rawRow12944 : Integer.Sparse Key := [(key1755, -6), (key1516, -6), (key1744, -6), (key1744, -6), (key1755, 6), (key1377, 6), (key1726, 6), (key1726, 6)]

theorem rawRowCheck12944 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form16 = rawRow12944 := by decide +kernel

def row12944 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

theorem rowCheck12944 : row12944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12944 := by decide +kernel

theorem rowEval12944 (x : Key → ℝ) : Integer.Sparse.eval row12944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12944, Integer.Sparse.eval_collectBalanced, rawRowCheck12944]

def rawRow12945 : Integer.Sparse Key := [(key1755, -6), (key1744, -6), (key1516, -6), (key1744, -6), (key1755, 6), (key1726, 6), (key1377, 6), (key1726, 6)]

theorem rawRowCheck12945 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form16 = rawRow12945 := by decide +kernel

def row12945 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

theorem rowCheck12945 : row12945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12945 := by decide +kernel

theorem rowEval12945 (x : Key → ℝ) : Integer.Sparse.eval row12945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12945, Integer.Sparse.eval_collectBalanced, rawRowCheck12945]

def rawRow12946 : Integer.Sparse Key := [(key1755, -6), (key1744, -6), (key1744, -6), (key1516, -6), (key1755, 6), (key1726, 6), (key1726, 6), (key1377, 6)]

theorem rawRowCheck12946 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form16 = rawRow12946 := by decide +kernel

def row12946 : Integer.Sparse Key := [(key1377, 6), (key1516, -6), (key1726, 12), (key1744, -12)]

theorem rowCheck12946 : row12946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12946 := by decide +kernel

theorem rowEval12946 (x : Key → ℝ) : Integer.Sparse.eval row12946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12946, Integer.Sparse.eval_collectBalanced, rawRowCheck12946]

def rawRow12947 : Integer.Sparse Key := [(key1366, -2), (key1370, -2), (key1370, -2), (key1718, -2), (key1747, -2), (key1747, -2), (key1865, -2), (key1865, -2), (key1880, -2), (key1880, -2), (key1883, -2), (key1883, -2), (key1366, 2), (key1379, 2), (key1379, 2), (key1492, 2), (key1519, 2), (key1519, 2), (key1870, 2), (key1870, 2), (key1880, 2), (key1880, 2), (key1891, 2), (key1891, 2)]

theorem rawRowCheck12947 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form17 = rawRow12947 := by decide +kernel

def row12947 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

theorem rowCheck12947 : row12947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12947 := by decide +kernel

theorem rowEval12947 (x : Key → ℝ) : Integer.Sparse.eval row12947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12947, Integer.Sparse.eval_collectBalanced, rawRowCheck12947]

def rawRow12948 : Integer.Sparse Key := [(key1370, -2), (key1366, -2), (key1370, -2), (key1747, -2), (key1718, -2), (key1747, -2), (key1880, -2), (key1883, -2), (key1865, -2), (key1883, -2), (key1865, -2), (key1880, -2), (key1379, 2), (key1366, 2), (key1379, 2), (key1519, 2), (key1492, 2), (key1519, 2), (key1880, 2), (key1891, 2), (key1870, 2), (key1891, 2), (key1870, 2), (key1880, 2)]

theorem rawRowCheck12948 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form17 = rawRow12948 := by decide +kernel

def row12948 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

theorem rowCheck12948 : row12948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12948 := by decide +kernel

theorem rowEval12948 (x : Key → ℝ) : Integer.Sparse.eval row12948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12948, Integer.Sparse.eval_collectBalanced, rawRowCheck12948]

def rawRow12949 : Integer.Sparse Key := [(key1370, -2), (key1370, -2), (key1366, -2), (key1747, -2), (key1747, -2), (key1718, -2), (key1883, -2), (key1880, -2), (key1883, -2), (key1865, -2), (key1880, -2), (key1865, -2), (key1379, 2), (key1379, 2), (key1366, 2), (key1519, 2), (key1519, 2), (key1492, 2), (key1891, 2), (key1880, 2), (key1891, 2), (key1870, 2), (key1880, 2), (key1870, 2)]

theorem rawRowCheck12949 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form17 = rawRow12949 := by decide +kernel

def row12949 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

theorem rowCheck12949 : row12949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12949 := by decide +kernel

theorem rowEval12949 (x : Key → ℝ) : Integer.Sparse.eval row12949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12949, Integer.Sparse.eval_collectBalanced, rawRowCheck12949]

def rawRow12950 : Integer.Sparse Key := [(key1718, -2), (key1865, -2), (key1865, -2), (key1366, -2), (key1880, -2), (key1880, -2), (key1370, -2), (key1370, -2), (key1747, -2), (key1747, -2), (key1883, -2), (key1883, -2), (key1492, 2), (key1870, 2), (key1870, 2), (key1366, 2), (key1880, 2), (key1880, 2), (key1379, 2), (key1379, 2), (key1519, 2), (key1519, 2), (key1891, 2), (key1891, 2)]

theorem rawRowCheck12950 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form17 = rawRow12950 := by decide +kernel

def row12950 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

theorem rowCheck12950 : row12950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12950 := by decide +kernel

theorem rowEval12950 (x : Key → ℝ) : Integer.Sparse.eval row12950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12950, Integer.Sparse.eval_collectBalanced, rawRowCheck12950]

def rawRow12951 : Integer.Sparse Key := [(key1865, -2), (key1718, -2), (key1865, -2), (key1880, -2), (key1366, -2), (key1880, -2), (key1747, -2), (key1883, -2), (key1370, -2), (key1883, -2), (key1370, -2), (key1747, -2), (key1870, 2), (key1492, 2), (key1870, 2), (key1880, 2), (key1366, 2), (key1880, 2), (key1519, 2), (key1891, 2), (key1379, 2), (key1891, 2), (key1379, 2), (key1519, 2)]

theorem rawRowCheck12951 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form17 = rawRow12951 := by decide +kernel

def row12951 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

theorem rowCheck12951 : row12951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12951 := by decide +kernel

theorem rowEval12951 (x : Key → ℝ) : Integer.Sparse.eval row12951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12951, Integer.Sparse.eval_collectBalanced, rawRowCheck12951]

def rawRow12952 : Integer.Sparse Key := [(key1865, -2), (key1865, -2), (key1718, -2), (key1880, -2), (key1880, -2), (key1366, -2), (key1883, -2), (key1747, -2), (key1883, -2), (key1370, -2), (key1747, -2), (key1370, -2), (key1870, 2), (key1870, 2), (key1492, 2), (key1880, 2), (key1880, 2), (key1366, 2), (key1891, 2), (key1519, 2), (key1891, 2), (key1379, 2), (key1519, 2), (key1379, 2)]

theorem rawRowCheck12952 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form17 = rawRow12952 := by decide +kernel

def row12952 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

theorem rowCheck12952 : row12952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12952 := by decide +kernel

theorem rowEval12952 (x : Key → ℝ) : Integer.Sparse.eval row12952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck12952, Integer.Sparse.eval_collectBalanced, rawRowCheck12952]

def rawRow12953 : Integer.Sparse Key := [(key1747, -2), (key1880, -2), (key1883, -2), (key1370, -2), (key1865, -2), (key1883, -2), (key1366, -2), (key1370, -2), (key1718, -2), (key1747, -2), (key1865, -2), (key1880, -2), (key1519, 2), (key1880, 2), (key1891, 2), (key1379, 2), (key1870, 2), (key1891, 2), (key1366, 2), (key1379, 2), (key1492, 2), (key1519, 2), (key1870, 2), (key1880, 2)]

theorem rawRowCheck12953 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form17 = rawRow12953 := by decide +kernel

def row12953 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

theorem rowCheck12953 : row12953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12953 := by decide +kernel

theorem rowEval12953 (x : Key → ℝ) : Integer.Sparse.eval row12953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12953, Integer.Sparse.eval_collectBalanced, rawRowCheck12953]

def rawRow12954 : Integer.Sparse Key := [(key1747, -2), (key1883, -2), (key1880, -2), (key1370, -2), (key1883, -2), (key1865, -2), (key1370, -2), (key1366, -2), (key1747, -2), (key1718, -2), (key1880, -2), (key1865, -2), (key1519, 2), (key1891, 2), (key1880, 2), (key1379, 2), (key1891, 2), (key1870, 2), (key1379, 2), (key1366, 2), (key1519, 2), (key1492, 2), (key1880, 2), (key1870, 2)]

theorem rawRowCheck12954 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form17 = rawRow12954 := by decide +kernel

def row12954 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

theorem rowCheck12954 : row12954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12954 := by decide +kernel

theorem rowEval12954 (x : Key → ℝ) : Integer.Sparse.eval row12954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12954, Integer.Sparse.eval_collectBalanced, rawRowCheck12954]

def rawRow12955 : Integer.Sparse Key := [(key1880, -2), (key1747, -2), (key1883, -2), (key1865, -2), (key1370, -2), (key1883, -2), (key1718, -2), (key1865, -2), (key1366, -2), (key1880, -2), (key1370, -2), (key1747, -2), (key1880, 2), (key1519, 2), (key1891, 2), (key1870, 2), (key1379, 2), (key1891, 2), (key1492, 2), (key1870, 2), (key1366, 2), (key1880, 2), (key1379, 2), (key1519, 2)]

theorem rawRowCheck12955 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form17 = rawRow12955 := by decide +kernel

def row12955 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

theorem rowCheck12955 : row12955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12955 := by decide +kernel

theorem rowEval12955 (x : Key → ℝ) : Integer.Sparse.eval row12955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12955, Integer.Sparse.eval_collectBalanced, rawRowCheck12955]

def rawRow12956 : Integer.Sparse Key := [(key1880, -2), (key1883, -2), (key1747, -2), (key1865, -2), (key1883, -2), (key1370, -2), (key1865, -2), (key1718, -2), (key1880, -2), (key1366, -2), (key1747, -2), (key1370, -2), (key1880, 2), (key1891, 2), (key1519, 2), (key1870, 2), (key1891, 2), (key1379, 2), (key1870, 2), (key1492, 2), (key1880, 2), (key1366, 2), (key1519, 2), (key1379, 2)]

theorem rawRowCheck12956 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form17 = rawRow12956 := by decide +kernel

def row12956 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

theorem rowCheck12956 : row12956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12956 := by decide +kernel

theorem rowEval12956 (x : Key → ℝ) : Integer.Sparse.eval row12956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck12956, Integer.Sparse.eval_collectBalanced, rawRowCheck12956]

def rawRow12957 : Integer.Sparse Key := [(key1883, -2), (key1747, -2), (key1880, -2), (key1883, -2), (key1370, -2), (key1865, -2), (key1747, -2), (key1880, -2), (key1370, -2), (key1865, -2), (key1366, -2), (key1718, -2), (key1891, 2), (key1519, 2), (key1880, 2), (key1891, 2), (key1379, 2), (key1870, 2), (key1519, 2), (key1880, 2), (key1379, 2), (key1870, 2), (key1366, 2), (key1492, 2)]

theorem rawRowCheck12957 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form17 = rawRow12957 := by decide +kernel

def row12957 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

theorem rowCheck12957 : row12957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12957 := by decide +kernel

theorem rowEval12957 (x : Key → ℝ) : Integer.Sparse.eval row12957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12957, Integer.Sparse.eval_collectBalanced, rawRowCheck12957]

def rawRow12958 : Integer.Sparse Key := [(key1883, -2), (key1880, -2), (key1747, -2), (key1883, -2), (key1865, -2), (key1370, -2), (key1880, -2), (key1747, -2), (key1865, -2), (key1370, -2), (key1718, -2), (key1366, -2), (key1891, 2), (key1880, 2), (key1519, 2), (key1891, 2), (key1870, 2), (key1379, 2), (key1880, 2), (key1519, 2), (key1870, 2), (key1379, 2), (key1492, 2), (key1366, 2)]

theorem rawRowCheck12958 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form17 = rawRow12958 := by decide +kernel

def row12958 : Integer.Sparse Key := [(key1370, -4), (key1379, 4), (key1492, 2), (key1519, 4), (key1718, -2), (key1747, -4), (key1865, -4), (key1870, 4), (key1883, -4), (key1891, 4)]

theorem rowCheck12958 : row12958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12958 := by decide +kernel

theorem rowEval12958 (x : Key → ℝ) : Integer.Sparse.eval row12958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck12958, Integer.Sparse.eval_collectBalanced, rawRowCheck12958]

def rawRow12959 : Integer.Sparse Key := [(key1379, -2), (key1379, -2), (key1381, -2), (key1728, -2), (key1728, -2), (key1761, -2), (key1870, -2), (key1872, -2), (key1870, -2), (key1891, -2), (key1872, -2), (key1891, -2), (key1370, 2), (key1370, 2), (key1381, 2), (key1496, 2), (key1496, 2), (key1522, 2), (key1865, 2), (key1872, 2), (key1865, 2), (key1883, 2), (key1872, 2), (key1883, 2)]

theorem rawRowCheck12959 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form17 = rawRow12959 := by decide +kernel

def row12959 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

theorem rowCheck12959 : row12959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12959 := by decide +kernel

theorem rowEval12959 (x : Key → ℝ) : Integer.Sparse.eval row12959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12959, Integer.Sparse.eval_collectBalanced, rawRowCheck12959]

def rawRow12960 : Integer.Sparse Key := [(key1379, -2), (key1381, -2), (key1379, -2), (key1728, -2), (key1761, -2), (key1728, -2), (key1872, -2), (key1870, -2), (key1891, -2), (key1870, -2), (key1891, -2), (key1872, -2), (key1370, 2), (key1381, 2), (key1370, 2), (key1496, 2), (key1522, 2), (key1496, 2), (key1872, 2), (key1865, 2), (key1883, 2), (key1865, 2), (key1883, 2), (key1872, 2)]

theorem rawRowCheck12960 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form17 = rawRow12960 := by decide +kernel

def row12960 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

theorem rowCheck12960 : row12960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12960 := by decide +kernel

theorem rowEval12960 (x : Key → ℝ) : Integer.Sparse.eval row12960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12960, Integer.Sparse.eval_collectBalanced, rawRowCheck12960]

def rawRow12961 : Integer.Sparse Key := [(key1381, -2), (key1379, -2), (key1379, -2), (key1761, -2), (key1728, -2), (key1728, -2), (key1891, -2), (key1891, -2), (key1872, -2), (key1872, -2), (key1870, -2), (key1870, -2), (key1381, 2), (key1370, 2), (key1370, 2), (key1522, 2), (key1496, 2), (key1496, 2), (key1883, 2), (key1883, 2), (key1872, 2), (key1872, 2), (key1865, 2), (key1865, 2)]

theorem rawRowCheck12961 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form17 = rawRow12961 := by decide +kernel

def row12961 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

theorem rowCheck12961 : row12961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12961 := by decide +kernel

theorem rowEval12961 (x : Key → ℝ) : Integer.Sparse.eval row12961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12961, Integer.Sparse.eval_collectBalanced, rawRowCheck12961]

def rawRow12962 : Integer.Sparse Key := [(key1728, -2), (key1870, -2), (key1872, -2), (key1379, -2), (key1870, -2), (key1891, -2), (key1379, -2), (key1381, -2), (key1728, -2), (key1761, -2), (key1872, -2), (key1891, -2), (key1496, 2), (key1865, 2), (key1872, 2), (key1370, 2), (key1865, 2), (key1883, 2), (key1370, 2), (key1381, 2), (key1496, 2), (key1522, 2), (key1872, 2), (key1883, 2)]

theorem rawRowCheck12962 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form17 = rawRow12962 := by decide +kernel

def row12962 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

theorem rowCheck12962 : row12962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12962 := by decide +kernel

theorem rowEval12962 (x : Key → ℝ) : Integer.Sparse.eval row12962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12962, Integer.Sparse.eval_collectBalanced, rawRowCheck12962]

def rawRow12963 : Integer.Sparse Key := [(key1728, -2), (key1872, -2), (key1870, -2), (key1379, -2), (key1891, -2), (key1870, -2), (key1381, -2), (key1379, -2), (key1761, -2), (key1728, -2), (key1891, -2), (key1872, -2), (key1496, 2), (key1872, 2), (key1865, 2), (key1370, 2), (key1883, 2), (key1865, 2), (key1381, 2), (key1370, 2), (key1522, 2), (key1496, 2), (key1883, 2), (key1872, 2)]

theorem rawRowCheck12963 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form17 = rawRow12963 := by decide +kernel

def row12963 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

theorem rowCheck12963 : row12963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12963 := by decide +kernel

theorem rowEval12963 (x : Key → ℝ) : Integer.Sparse.eval row12963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12963, Integer.Sparse.eval_collectBalanced, rawRowCheck12963]

def rawRow12964 : Integer.Sparse Key := [(key1870, -2), (key1728, -2), (key1872, -2), (key1870, -2), (key1379, -2), (key1891, -2), (key1728, -2), (key1872, -2), (key1379, -2), (key1891, -2), (key1381, -2), (key1761, -2), (key1865, 2), (key1496, 2), (key1872, 2), (key1865, 2), (key1370, 2), (key1883, 2), (key1496, 2), (key1872, 2), (key1370, 2), (key1883, 2), (key1381, 2), (key1522, 2)]

theorem rawRowCheck12964 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form17 = rawRow12964 := by decide +kernel

def row12964 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

theorem rowCheck12964 : row12964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12964 := by decide +kernel

theorem rowEval12964 (x : Key → ℝ) : Integer.Sparse.eval row12964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form17) x := by
  rw [rowCheck12964, Integer.Sparse.eval_collectBalanced, rawRowCheck12964]

def rawRow12965 : Integer.Sparse Key := [(key1870, -2), (key1872, -2), (key1728, -2), (key1870, -2), (key1891, -2), (key1379, -2), (key1872, -2), (key1728, -2), (key1891, -2), (key1379, -2), (key1761, -2), (key1381, -2), (key1865, 2), (key1872, 2), (key1496, 2), (key1865, 2), (key1883, 2), (key1370, 2), (key1872, 2), (key1496, 2), (key1883, 2), (key1370, 2), (key1522, 2), (key1381, 2)]

theorem rawRowCheck12965 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form17 = rawRow12965 := by decide +kernel

def row12965 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

theorem rowCheck12965 : row12965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12965 := by decide +kernel

theorem rowEval12965 (x : Key → ℝ) : Integer.Sparse.eval row12965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck12965, Integer.Sparse.eval_collectBalanced, rawRowCheck12965]

def rawRow12966 : Integer.Sparse Key := [(key1872, -2), (key1728, -2), (key1870, -2), (key1891, -2), (key1379, -2), (key1870, -2), (key1761, -2), (key1891, -2), (key1381, -2), (key1872, -2), (key1379, -2), (key1728, -2), (key1872, 2), (key1496, 2), (key1865, 2), (key1883, 2), (key1370, 2), (key1865, 2), (key1522, 2), (key1883, 2), (key1381, 2), (key1872, 2), (key1370, 2), (key1496, 2)]

theorem rawRowCheck12966 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form17 = rawRow12966 := by decide +kernel

def row12966 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

theorem rowCheck12966 : row12966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12966 := by decide +kernel

theorem rowEval12966 (x : Key → ℝ) : Integer.Sparse.eval row12966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12966, Integer.Sparse.eval_collectBalanced, rawRowCheck12966]

def rawRow12967 : Integer.Sparse Key := [(key1872, -2), (key1870, -2), (key1728, -2), (key1891, -2), (key1870, -2), (key1379, -2), (key1891, -2), (key1761, -2), (key1872, -2), (key1381, -2), (key1728, -2), (key1379, -2), (key1872, 2), (key1865, 2), (key1496, 2), (key1883, 2), (key1865, 2), (key1370, 2), (key1883, 2), (key1522, 2), (key1872, 2), (key1381, 2), (key1496, 2), (key1370, 2)]

theorem rawRowCheck12967 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form17 = rawRow12967 := by decide +kernel

def row12967 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

theorem rowCheck12967 : row12967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12967 := by decide +kernel

theorem rowEval12967 (x : Key → ℝ) : Integer.Sparse.eval row12967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck12967, Integer.Sparse.eval_collectBalanced, rawRowCheck12967]

def rawRow12968 : Integer.Sparse Key := [(key1761, -2), (key1891, -2), (key1891, -2), (key1381, -2), (key1872, -2), (key1872, -2), (key1379, -2), (key1379, -2), (key1728, -2), (key1728, -2), (key1870, -2), (key1870, -2), (key1522, 2), (key1883, 2), (key1883, 2), (key1381, 2), (key1872, 2), (key1872, 2), (key1370, 2), (key1370, 2), (key1496, 2), (key1496, 2), (key1865, 2), (key1865, 2)]

theorem rawRowCheck12968 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form17 = rawRow12968 := by decide +kernel

def row12968 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

theorem rowCheck12968 : row12968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12968 := by decide +kernel

theorem rowEval12968 (x : Key → ℝ) : Integer.Sparse.eval row12968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12968, Integer.Sparse.eval_collectBalanced, rawRowCheck12968]

def rawRow12969 : Integer.Sparse Key := [(key1891, -2), (key1761, -2), (key1891, -2), (key1872, -2), (key1381, -2), (key1872, -2), (key1728, -2), (key1870, -2), (key1379, -2), (key1870, -2), (key1379, -2), (key1728, -2), (key1883, 2), (key1522, 2), (key1883, 2), (key1872, 2), (key1381, 2), (key1872, 2), (key1496, 2), (key1865, 2), (key1370, 2), (key1865, 2), (key1370, 2), (key1496, 2)]

theorem rawRowCheck12969 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form17 = rawRow12969 := by decide +kernel

def row12969 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

theorem rowCheck12969 : row12969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12969 := by decide +kernel

theorem rowEval12969 (x : Key → ℝ) : Integer.Sparse.eval row12969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12969, Integer.Sparse.eval_collectBalanced, rawRowCheck12969]

def rawRow12970 : Integer.Sparse Key := [(key1891, -2), (key1891, -2), (key1761, -2), (key1872, -2), (key1872, -2), (key1381, -2), (key1870, -2), (key1728, -2), (key1870, -2), (key1379, -2), (key1728, -2), (key1379, -2), (key1883, 2), (key1883, 2), (key1522, 2), (key1872, 2), (key1872, 2), (key1381, 2), (key1865, 2), (key1496, 2), (key1865, 2), (key1370, 2), (key1496, 2), (key1370, 2)]

theorem rawRowCheck12970 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form17 = rawRow12970 := by decide +kernel

def row12970 : Integer.Sparse Key := [(key1370, 4), (key1379, -4), (key1496, 4), (key1522, 2), (key1728, -4), (key1761, -2), (key1865, 4), (key1870, -4), (key1883, 4), (key1891, -4)]

theorem rowCheck12970 : row12970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12970 := by decide +kernel

theorem rowEval12970 (x : Key → ℝ) : Integer.Sparse.eval row12970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck12970, Integer.Sparse.eval_collectBalanced, rawRowCheck12970]

def rawRow12971 : Integer.Sparse Key := [(key227, 2), (key231, 2), (key231, 2), (key499, 2), (key560, 2), (key560, 2), (key623, 2), (key623, 2), (key649, 2), (key649, 2), (key653, 2), (key653, 2), (key231, -2), (key231, -2), (key233, -2), (key503, -2), (key503, -2), (key560, -2), (key560, -2), (key564, -2), (key564, -2), (key625, -2), (key653, -2), (key653, -2)]

theorem rawRowCheck12971 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form18 = rawRow12971 := by decide +kernel

def row12971 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

theorem rowCheck12971 : row12971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12971 := by decide +kernel

theorem rowEval12971 (x : Key → ℝ) : Integer.Sparse.eval row12971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12971, Integer.Sparse.eval_collectBalanced, rawRowCheck12971]

def rawRow12972 : Integer.Sparse Key := [(key231, 2), (key227, 2), (key231, 2), (key560, 2), (key499, 2), (key560, 2), (key649, 2), (key653, 2), (key623, 2), (key653, 2), (key623, 2), (key649, 2), (key231, -2), (key233, -2), (key231, -2), (key560, -2), (key564, -2), (key503, -2), (key564, -2), (key503, -2), (key560, -2), (key653, -2), (key625, -2), (key653, -2)]

theorem rawRowCheck12972 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form18 = rawRow12972 := by decide +kernel

def row12972 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

theorem rowCheck12972 : row12972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12972 := by decide +kernel

theorem rowEval12972 (x : Key → ℝ) : Integer.Sparse.eval row12972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12972, Integer.Sparse.eval_collectBalanced, rawRowCheck12972]

def rawRow12973 : Integer.Sparse Key := [(key231, 2), (key231, 2), (key227, 2), (key560, 2), (key560, 2), (key499, 2), (key653, 2), (key649, 2), (key653, 2), (key623, 2), (key649, 2), (key623, 2), (key233, -2), (key231, -2), (key231, -2), (key564, -2), (key560, -2), (key564, -2), (key503, -2), (key560, -2), (key503, -2), (key653, -2), (key653, -2), (key625, -2)]

theorem rawRowCheck12973 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form18 = rawRow12973 := by decide +kernel

def row12973 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

theorem rowCheck12973 : row12973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12973 := by decide +kernel

theorem rowEval12973 (x : Key → ℝ) : Integer.Sparse.eval row12973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12973, Integer.Sparse.eval_collectBalanced, rawRowCheck12973]

def rawRow12974 : Integer.Sparse Key := [(key499, 2), (key623, 2), (key623, 2), (key227, 2), (key649, 2), (key649, 2), (key231, 2), (key231, 2), (key560, 2), (key560, 2), (key653, 2), (key653, 2), (key503, -2), (key503, -2), (key625, -2), (key231, -2), (key231, -2), (key560, -2), (key560, -2), (key653, -2), (key653, -2), (key233, -2), (key564, -2), (key564, -2)]

theorem rawRowCheck12974 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form18 = rawRow12974 := by decide +kernel

def row12974 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

theorem rowCheck12974 : row12974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12974 := by decide +kernel

theorem rowEval12974 (x : Key → ℝ) : Integer.Sparse.eval row12974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12974, Integer.Sparse.eval_collectBalanced, rawRowCheck12974]

def rawRow12975 : Integer.Sparse Key := [(key623, 2), (key499, 2), (key623, 2), (key649, 2), (key227, 2), (key649, 2), (key560, 2), (key653, 2), (key231, 2), (key653, 2), (key231, 2), (key560, 2), (key503, -2), (key625, -2), (key503, -2), (key560, -2), (key653, -2), (key231, -2), (key653, -2), (key231, -2), (key560, -2), (key564, -2), (key233, -2), (key564, -2)]

theorem rawRowCheck12975 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form18 = rawRow12975 := by decide +kernel

def row12975 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

theorem rowCheck12975 : row12975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12975 := by decide +kernel

theorem rowEval12975 (x : Key → ℝ) : Integer.Sparse.eval row12975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12975, Integer.Sparse.eval_collectBalanced, rawRowCheck12975]

def rawRow12976 : Integer.Sparse Key := [(key623, 2), (key623, 2), (key499, 2), (key649, 2), (key649, 2), (key227, 2), (key653, 2), (key560, 2), (key653, 2), (key231, 2), (key560, 2), (key231, 2), (key625, -2), (key503, -2), (key503, -2), (key653, -2), (key560, -2), (key653, -2), (key231, -2), (key560, -2), (key231, -2), (key564, -2), (key564, -2), (key233, -2)]

theorem rawRowCheck12976 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form18 = rawRow12976 := by decide +kernel

def row12976 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

theorem rowCheck12976 : row12976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12976 := by decide +kernel

theorem rowEval12976 (x : Key → ℝ) : Integer.Sparse.eval row12976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck12976, Integer.Sparse.eval_collectBalanced, rawRowCheck12976]

def rawRow12977 : Integer.Sparse Key := [(key560, 2), (key649, 2), (key653, 2), (key231, 2), (key623, 2), (key653, 2), (key227, 2), (key231, 2), (key499, 2), (key560, 2), (key623, 2), (key649, 2), (key560, -2), (key564, -2), (key653, -2), (key231, -2), (key233, -2), (key503, -2), (key564, -2), (key625, -2), (key653, -2), (key231, -2), (key503, -2), (key560, -2)]

theorem rawRowCheck12977 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form18 = rawRow12977 := by decide +kernel

def row12977 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

theorem rowCheck12977 : row12977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12977 := by decide +kernel

theorem rowEval12977 (x : Key → ℝ) : Integer.Sparse.eval row12977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12977, Integer.Sparse.eval_collectBalanced, rawRowCheck12977]

def rawRow12978 : Integer.Sparse Key := [(key560, 2), (key653, 2), (key649, 2), (key231, 2), (key653, 2), (key623, 2), (key231, 2), (key227, 2), (key560, 2), (key499, 2), (key649, 2), (key623, 2), (key564, -2), (key560, -2), (key653, -2), (key233, -2), (key231, -2), (key564, -2), (key503, -2), (key653, -2), (key625, -2), (key231, -2), (key560, -2), (key503, -2)]

theorem rawRowCheck12978 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form18 = rawRow12978 := by decide +kernel

def row12978 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

theorem rowCheck12978 : row12978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12978 := by decide +kernel

theorem rowEval12978 (x : Key → ℝ) : Integer.Sparse.eval row12978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12978, Integer.Sparse.eval_collectBalanced, rawRowCheck12978]

def rawRow12979 : Integer.Sparse Key := [(key649, 2), (key560, 2), (key653, 2), (key623, 2), (key231, 2), (key653, 2), (key499, 2), (key623, 2), (key227, 2), (key649, 2), (key231, 2), (key560, 2), (key560, -2), (key653, -2), (key564, -2), (key503, -2), (key625, -2), (key231, -2), (key653, -2), (key233, -2), (key564, -2), (key503, -2), (key231, -2), (key560, -2)]

theorem rawRowCheck12979 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form18 = rawRow12979 := by decide +kernel

def row12979 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

theorem rowCheck12979 : row12979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12979 := by decide +kernel

theorem rowEval12979 (x : Key → ℝ) : Integer.Sparse.eval row12979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12979, Integer.Sparse.eval_collectBalanced, rawRowCheck12979]

def rawRow12980 : Integer.Sparse Key := [(key649, 2), (key653, 2), (key560, 2), (key623, 2), (key653, 2), (key231, 2), (key623, 2), (key499, 2), (key649, 2), (key227, 2), (key560, 2), (key231, 2), (key653, -2), (key560, -2), (key564, -2), (key625, -2), (key503, -2), (key653, -2), (key231, -2), (key564, -2), (key233, -2), (key503, -2), (key560, -2), (key231, -2)]

theorem rawRowCheck12980 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form18 = rawRow12980 := by decide +kernel

def row12980 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

theorem rowCheck12980 : row12980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12980 := by decide +kernel

theorem rowEval12980 (x : Key → ℝ) : Integer.Sparse.eval row12980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck12980, Integer.Sparse.eval_collectBalanced, rawRowCheck12980]

def rawRow12981 : Integer.Sparse Key := [(key653, 2), (key560, 2), (key649, 2), (key653, 2), (key231, 2), (key623, 2), (key560, 2), (key649, 2), (key231, 2), (key623, 2), (key227, 2), (key499, 2), (key564, -2), (key653, -2), (key560, -2), (key564, -2), (key653, -2), (key233, -2), (key625, -2), (key231, -2), (key503, -2), (key560, -2), (key231, -2), (key503, -2)]

theorem rawRowCheck12981 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form18 = rawRow12981 := by decide +kernel

def row12981 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

theorem rowCheck12981 : row12981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12981 := by decide +kernel

theorem rowEval12981 (x : Key → ℝ) : Integer.Sparse.eval row12981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12981, Integer.Sparse.eval_collectBalanced, rawRowCheck12981]

def rawRow12982 : Integer.Sparse Key := [(key653, 2), (key649, 2), (key560, 2), (key653, 2), (key623, 2), (key231, 2), (key649, 2), (key560, 2), (key623, 2), (key231, 2), (key499, 2), (key227, 2), (key653, -2), (key564, -2), (key560, -2), (key653, -2), (key564, -2), (key625, -2), (key233, -2), (key503, -2), (key231, -2), (key560, -2), (key503, -2), (key231, -2)]

theorem rawRowCheck12982 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form18 = rawRow12982 := by decide +kernel

def row12982 : Integer.Sparse Key := [(key227, 2), (key233, -2), (key499, 2), (key503, -4), (key564, -4), (key623, 4), (key625, -2), (key649, 4)]

theorem rowCheck12982 : row12982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12982 := by decide +kernel

theorem rowEval12982 (x : Key → ℝ) : Integer.Sparse.eval row12982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck12982, Integer.Sparse.eval_collectBalanced, rawRowCheck12982]

def rawRow12983 : Integer.Sparse Key := [(key231, 2), (key231, 2), (key233, 2), (key503, 2), (key503, 2), (key564, 2), (key623, 2), (key625, 2), (key623, 2), (key653, 2), (key625, 2), (key653, 2), (key227, -2), (key231, -2), (key231, -2), (key499, -2), (key503, -2), (key499, -2), (key560, -2), (key503, -2), (key560, -2), (key623, -2), (key623, -2), (key649, -2)]

theorem rawRowCheck12983 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form18 = rawRow12983 := by decide +kernel

def row12983 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

theorem rowCheck12983 : row12983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12983 := by decide +kernel

theorem rowEval12983 (x : Key → ℝ) : Integer.Sparse.eval row12983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12983, Integer.Sparse.eval_collectBalanced, rawRowCheck12983]

def rawRow12984 : Integer.Sparse Key := [(key231, 2), (key233, 2), (key231, 2), (key503, 2), (key564, 2), (key503, 2), (key625, 2), (key623, 2), (key653, 2), (key623, 2), (key653, 2), (key625, 2), (key231, -2), (key227, -2), (key231, -2), (key503, -2), (key499, -2), (key560, -2), (key499, -2), (key560, -2), (key503, -2), (key623, -2), (key649, -2), (key623, -2)]

theorem rawRowCheck12984 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form18 = rawRow12984 := by decide +kernel

def row12984 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

theorem rowCheck12984 : row12984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12984 := by decide +kernel

theorem rowEval12984 (x : Key → ℝ) : Integer.Sparse.eval row12984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12984, Integer.Sparse.eval_collectBalanced, rawRowCheck12984]

def rawRow12985 : Integer.Sparse Key := [(key233, 2), (key231, 2), (key231, 2), (key564, 2), (key503, 2), (key503, 2), (key653, 2), (key653, 2), (key625, 2), (key625, 2), (key623, 2), (key623, 2), (key231, -2), (key231, -2), (key227, -2), (key560, -2), (key560, -2), (key503, -2), (key503, -2), (key499, -2), (key499, -2), (key649, -2), (key623, -2), (key623, -2)]

theorem rawRowCheck12985 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form18 = rawRow12985 := by decide +kernel

def row12985 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

theorem rowCheck12985 : row12985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12985 := by decide +kernel

theorem rowEval12985 (x : Key → ℝ) : Integer.Sparse.eval row12985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12985, Integer.Sparse.eval_collectBalanced, rawRowCheck12985]

def rawRow12986 : Integer.Sparse Key := [(key503, 2), (key623, 2), (key625, 2), (key231, 2), (key623, 2), (key653, 2), (key231, 2), (key233, 2), (key503, 2), (key564, 2), (key625, 2), (key653, 2), (key499, -2), (key503, -2), (key623, -2), (key227, -2), (key231, -2), (key499, -2), (key560, -2), (key623, -2), (key649, -2), (key231, -2), (key503, -2), (key560, -2)]

theorem rawRowCheck12986 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form18 = rawRow12986 := by decide +kernel

def row12986 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

theorem rowCheck12986 : row12986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12986 := by decide +kernel

theorem rowEval12986 (x : Key → ℝ) : Integer.Sparse.eval row12986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12986, Integer.Sparse.eval_collectBalanced, rawRowCheck12986]

def rawRow12987 : Integer.Sparse Key := [(key503, 2), (key625, 2), (key623, 2), (key231, 2), (key653, 2), (key623, 2), (key233, 2), (key231, 2), (key564, 2), (key503, 2), (key653, 2), (key625, 2), (key503, -2), (key499, -2), (key623, -2), (key231, -2), (key227, -2), (key560, -2), (key499, -2), (key649, -2), (key623, -2), (key231, -2), (key560, -2), (key503, -2)]

theorem rawRowCheck12987 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form18 = rawRow12987 := by decide +kernel

def row12987 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

theorem rowCheck12987 : row12987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12987 := by decide +kernel

theorem rowEval12987 (x : Key → ℝ) : Integer.Sparse.eval row12987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12987, Integer.Sparse.eval_collectBalanced, rawRowCheck12987]

def rawRow12988 : Integer.Sparse Key := [(key623, 2), (key503, 2), (key625, 2), (key623, 2), (key231, 2), (key653, 2), (key503, 2), (key625, 2), (key231, 2), (key653, 2), (key233, 2), (key564, 2), (key499, -2), (key623, -2), (key503, -2), (key499, -2), (key623, -2), (key227, -2), (key649, -2), (key231, -2), (key560, -2), (key503, -2), (key231, -2), (key560, -2)]

theorem rawRowCheck12988 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form18 = rawRow12988 := by decide +kernel

def row12988 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

theorem rowCheck12988 : row12988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12988 := by decide +kernel

theorem rowEval12988 (x : Key → ℝ) : Integer.Sparse.eval row12988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form18) x := by
  rw [rowCheck12988, Integer.Sparse.eval_collectBalanced, rawRowCheck12988]

def rawRow12989 : Integer.Sparse Key := [(key623, 2), (key625, 2), (key503, 2), (key623, 2), (key653, 2), (key231, 2), (key625, 2), (key503, 2), (key653, 2), (key231, 2), (key564, 2), (key233, 2), (key623, -2), (key499, -2), (key503, -2), (key623, -2), (key499, -2), (key649, -2), (key227, -2), (key560, -2), (key231, -2), (key503, -2), (key560, -2), (key231, -2)]

theorem rawRowCheck12989 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form18 = rawRow12989 := by decide +kernel

def row12989 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

theorem rowCheck12989 : row12989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12989 := by decide +kernel

theorem rowEval12989 (x : Key → ℝ) : Integer.Sparse.eval row12989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck12989, Integer.Sparse.eval_collectBalanced, rawRowCheck12989]

def rawRow12990 : Integer.Sparse Key := [(key625, 2), (key503, 2), (key623, 2), (key653, 2), (key231, 2), (key623, 2), (key564, 2), (key653, 2), (key233, 2), (key625, 2), (key231, 2), (key503, 2), (key503, -2), (key623, -2), (key499, -2), (key560, -2), (key649, -2), (key231, -2), (key623, -2), (key227, -2), (key499, -2), (key560, -2), (key231, -2), (key503, -2)]

theorem rawRowCheck12990 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form18 = rawRow12990 := by decide +kernel

def row12990 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

theorem rowCheck12990 : row12990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12990 := by decide +kernel

theorem rowEval12990 (x : Key → ℝ) : Integer.Sparse.eval row12990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12990, Integer.Sparse.eval_collectBalanced, rawRowCheck12990]

def rawRow12991 : Integer.Sparse Key := [(key625, 2), (key623, 2), (key503, 2), (key653, 2), (key623, 2), (key231, 2), (key653, 2), (key564, 2), (key625, 2), (key233, 2), (key503, 2), (key231, 2), (key623, -2), (key503, -2), (key499, -2), (key649, -2), (key560, -2), (key623, -2), (key231, -2), (key499, -2), (key227, -2), (key560, -2), (key503, -2), (key231, -2)]

theorem rawRowCheck12991 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form18 = rawRow12991 := by decide +kernel

def row12991 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

theorem rowCheck12991 : row12991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12991 := by decide +kernel

theorem rowEval12991 (x : Key → ℝ) : Integer.Sparse.eval row12991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck12991, Integer.Sparse.eval_collectBalanced, rawRowCheck12991]

def rawRow12992 : Integer.Sparse Key := [(key564, 2), (key653, 2), (key653, 2), (key233, 2), (key625, 2), (key625, 2), (key231, 2), (key231, 2), (key503, 2), (key503, 2), (key623, 2), (key623, 2), (key560, -2), (key560, -2), (key649, -2), (key231, -2), (key231, -2), (key503, -2), (key503, -2), (key623, -2), (key623, -2), (key227, -2), (key499, -2), (key499, -2)]

theorem rawRowCheck12992 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form18 = rawRow12992 := by decide +kernel

def row12992 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

theorem rowCheck12992 : row12992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12992 := by decide +kernel

theorem rowEval12992 (x : Key → ℝ) : Integer.Sparse.eval row12992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12992, Integer.Sparse.eval_collectBalanced, rawRowCheck12992]

def rawRow12993 : Integer.Sparse Key := [(key653, 2), (key564, 2), (key653, 2), (key625, 2), (key233, 2), (key625, 2), (key503, 2), (key623, 2), (key231, 2), (key623, 2), (key231, 2), (key503, 2), (key560, -2), (key649, -2), (key560, -2), (key503, -2), (key623, -2), (key231, -2), (key623, -2), (key231, -2), (key503, -2), (key499, -2), (key227, -2), (key499, -2)]

theorem rawRowCheck12993 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form18 = rawRow12993 := by decide +kernel

def row12993 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

theorem rowCheck12993 : row12993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12993 := by decide +kernel

theorem rowEval12993 (x : Key → ℝ) : Integer.Sparse.eval row12993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12993, Integer.Sparse.eval_collectBalanced, rawRowCheck12993]

def rawRow12994 : Integer.Sparse Key := [(key653, 2), (key653, 2), (key564, 2), (key625, 2), (key625, 2), (key233, 2), (key623, 2), (key503, 2), (key623, 2), (key231, 2), (key503, 2), (key231, 2), (key649, -2), (key560, -2), (key560, -2), (key623, -2), (key503, -2), (key623, -2), (key231, -2), (key503, -2), (key231, -2), (key499, -2), (key499, -2), (key227, -2)]

theorem rawRowCheck12994 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form18 = rawRow12994 := by decide +kernel

def row12994 : Integer.Sparse Key := [(key227, -2), (key233, 2), (key499, -4), (key560, -4), (key564, 2), (key625, 4), (key649, -2), (key653, 4)]

theorem rowCheck12994 : row12994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12994 := by decide +kernel

theorem rowEval12994 (x : Key → ℝ) : Integer.Sparse.eval row12994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck12994, Integer.Sparse.eval_collectBalanced, rawRowCheck12994]

def rawRow12995 : Integer.Sparse Key := [(key1505, -4), (key1509, -4), (key1509, -4), (key1738, -4), (key1738, -4), (key1745, -4), (key1509, 6), (key1509, 6), (key1517, 6), (key1745, 6)]

theorem rawRowCheck12995 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form19 = rawRow12995 := by decide +kernel

def row12995 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

theorem rowCheck12995 : row12995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12995 := by decide +kernel

theorem rowEval12995 (x : Key → ℝ) : Integer.Sparse.eval row12995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12995, Integer.Sparse.eval_collectBalanced, rawRowCheck12995]

def rawRow12996 : Integer.Sparse Key := [(key1509, -4), (key1505, -4), (key1509, -4), (key1738, -4), (key1745, -4), (key1738, -4), (key1509, 6), (key1517, 6), (key1509, 6), (key1745, 6)]

theorem rawRowCheck12996 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form19 = rawRow12996 := by decide +kernel

def row12996 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

theorem rowCheck12996 : row12996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12996 := by decide +kernel

theorem rowEval12996 (x : Key → ℝ) : Integer.Sparse.eval row12996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12996, Integer.Sparse.eval_collectBalanced, rawRowCheck12996]

def rawRow12997 : Integer.Sparse Key := [(key1509, -4), (key1509, -4), (key1505, -4), (key1745, -4), (key1738, -4), (key1738, -4), (key1517, 6), (key1509, 6), (key1509, 6), (key1745, 6)]

theorem rawRowCheck12997 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form19 = rawRow12997 := by decide +kernel

def row12997 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

theorem rowCheck12997 : row12997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12997 := by decide +kernel

theorem rowEval12997 (x : Key → ℝ) : Integer.Sparse.eval row12997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12997, Integer.Sparse.eval_collectBalanced, rawRowCheck12997]

def rawRow12998 : Integer.Sparse Key := [(key1505, -4), (key1738, -4), (key1738, -4), (key1509, -4), (key1509, -4), (key1745, -4), (key1509, 6), (key1509, 6), (key1745, 6), (key1517, 6)]

theorem rawRowCheck12998 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form19 = rawRow12998 := by decide +kernel

def row12998 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

theorem rowCheck12998 : row12998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12998 := by decide +kernel

theorem rowEval12998 (x : Key → ℝ) : Integer.Sparse.eval row12998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12998, Integer.Sparse.eval_collectBalanced, rawRowCheck12998]

def rawRow12999 : Integer.Sparse Key := [(key1738, -4), (key1505, -4), (key1738, -4), (key1509, -4), (key1745, -4), (key1509, -4), (key1509, 6), (key1745, 6), (key1509, 6), (key1517, 6)]

theorem rawRowCheck12999 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form19 = rawRow12999 := by decide +kernel

def row12999 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

theorem rowCheck12999 : row12999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12999 := by decide +kernel

theorem rowEval12999 (x : Key → ℝ) : Integer.Sparse.eval row12999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck12999, Integer.Sparse.eval_collectBalanced, rawRowCheck12999]

def rawRow13000 : Integer.Sparse Key := [(key1738, -4), (key1738, -4), (key1505, -4), (key1745, -4), (key1509, -4), (key1509, -4), (key1745, 6), (key1509, 6), (key1509, 6), (key1517, 6)]

theorem rawRowCheck13000 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form19 = rawRow13000 := by decide +kernel

def row13000 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

theorem rowCheck13000 : row13000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13000 := by decide +kernel

theorem rowEval13000 (x : Key → ℝ) : Integer.Sparse.eval row13000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck13000, Integer.Sparse.eval_collectBalanced, rawRowCheck13000]

def rawRow13001 : Integer.Sparse Key := [(key1509, -4), (key1738, -4), (key1745, -4), (key1505, -4), (key1509, -4), (key1738, -4), (key1509, 6), (key1517, 6), (key1745, 6), (key1509, 6)]

theorem rawRowCheck13001 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form19 = rawRow13001 := by decide +kernel

def row13001 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

theorem rowCheck13001 : row13001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13001 := by decide +kernel

theorem rowEval13001 (x : Key → ℝ) : Integer.Sparse.eval row13001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck13001, Integer.Sparse.eval_collectBalanced, rawRowCheck13001]

def rawRow13002 : Integer.Sparse Key := [(key1509, -4), (key1745, -4), (key1738, -4), (key1509, -4), (key1505, -4), (key1738, -4), (key1517, 6), (key1509, 6), (key1745, 6), (key1509, 6)]

theorem rawRowCheck13002 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form19 = rawRow13002 := by decide +kernel

def row13002 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

theorem rowCheck13002 : row13002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13002 := by decide +kernel

theorem rowEval13002 (x : Key → ℝ) : Integer.Sparse.eval row13002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck13002, Integer.Sparse.eval_collectBalanced, rawRowCheck13002]

def rawRow13003 : Integer.Sparse Key := [(key1738, -4), (key1509, -4), (key1745, -4), (key1505, -4), (key1738, -4), (key1509, -4), (key1509, 6), (key1745, 6), (key1517, 6), (key1509, 6)]

theorem rawRowCheck13003 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form19 = rawRow13003 := by decide +kernel

def row13003 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

theorem rowCheck13003 : row13003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13003 := by decide +kernel

theorem rowEval13003 (x : Key → ℝ) : Integer.Sparse.eval row13003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck13003, Integer.Sparse.eval_collectBalanced, rawRowCheck13003]

def rawRow13004 : Integer.Sparse Key := [(key1738, -4), (key1745, -4), (key1509, -4), (key1738, -4), (key1505, -4), (key1509, -4), (key1745, 6), (key1509, 6), (key1517, 6), (key1509, 6)]

theorem rawRowCheck13004 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form19 = rawRow13004 := by decide +kernel

def row13004 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

theorem rowCheck13004 : row13004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13004 := by decide +kernel

theorem rowEval13004 (x : Key → ℝ) : Integer.Sparse.eval row13004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck13004, Integer.Sparse.eval_collectBalanced, rawRowCheck13004]

def rawRow13005 : Integer.Sparse Key := [(key1745, -4), (key1509, -4), (key1738, -4), (key1509, -4), (key1738, -4), (key1505, -4), (key1517, 6), (key1745, 6), (key1509, 6), (key1509, 6)]

theorem rawRowCheck13005 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form19 = rawRow13005 := by decide +kernel

def row13005 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

theorem rowCheck13005 : row13005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13005 := by decide +kernel

theorem rowEval13005 (x : Key → ℝ) : Integer.Sparse.eval row13005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck13005, Integer.Sparse.eval_collectBalanced, rawRowCheck13005]

def rawRow13006 : Integer.Sparse Key := [(key1745, -4), (key1738, -4), (key1509, -4), (key1738, -4), (key1509, -4), (key1505, -4), (key1745, 6), (key1517, 6), (key1509, 6), (key1509, 6)]

theorem rawRowCheck13006 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form19 = rawRow13006 := by decide +kernel

def row13006 : Integer.Sparse Key := [(key1505, -4), (key1509, 4), (key1517, 6), (key1738, -8), (key1745, 2)]

theorem rowCheck13006 : row13006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13006 := by decide +kernel

theorem rowEval13006 (x : Key → ℝ) : Integer.Sparse.eval row13006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck13006, Integer.Sparse.eval_collectBalanced, rawRowCheck13006]

def rawRow13007 : Integer.Sparse Key := [(key1509, -4), (key1509, -4), (key1517, -4), (key1738, -4), (key1745, -4), (key1745, -4), (key1505, 6), (key1509, 6), (key1509, 6), (key1738, 6)]

theorem rawRowCheck13007 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form19 = rawRow13007 := by decide +kernel

def row13007 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

theorem rowCheck13007 : row13007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13007 := by decide +kernel

theorem rowEval13007 (x : Key → ℝ) : Integer.Sparse.eval row13007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck13007, Integer.Sparse.eval_collectBalanced, rawRowCheck13007]

def rawRow13008 : Integer.Sparse Key := [(key1509, -4), (key1517, -4), (key1509, -4), (key1745, -4), (key1738, -4), (key1745, -4), (key1509, 6), (key1505, 6), (key1509, 6), (key1738, 6)]

theorem rawRowCheck13008 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form19 = rawRow13008 := by decide +kernel

def row13008 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

theorem rowCheck13008 : row13008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13008 := by decide +kernel

theorem rowEval13008 (x : Key → ℝ) : Integer.Sparse.eval row13008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck13008, Integer.Sparse.eval_collectBalanced, rawRowCheck13008]

def rawRow13009 : Integer.Sparse Key := [(key1517, -4), (key1509, -4), (key1509, -4), (key1745, -4), (key1745, -4), (key1738, -4), (key1509, 6), (key1509, 6), (key1505, 6), (key1738, 6)]

theorem rawRowCheck13009 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form19 = rawRow13009 := by decide +kernel

def row13009 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

theorem rowCheck13009 : row13009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13009 := by decide +kernel

theorem rowEval13009 (x : Key → ℝ) : Integer.Sparse.eval row13009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck13009, Integer.Sparse.eval_collectBalanced, rawRowCheck13009]

def rawRow13010 : Integer.Sparse Key := [(key1509, -4), (key1738, -4), (key1745, -4), (key1509, -4), (key1517, -4), (key1745, -4), (key1505, 6), (key1509, 6), (key1738, 6), (key1509, 6)]

theorem rawRowCheck13010 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form19 = rawRow13010 := by decide +kernel

def row13010 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

theorem rowCheck13010 : row13010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13010 := by decide +kernel

theorem rowEval13010 (x : Key → ℝ) : Integer.Sparse.eval row13010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck13010, Integer.Sparse.eval_collectBalanced, rawRowCheck13010]

def rawRow13011 : Integer.Sparse Key := [(key1509, -4), (key1745, -4), (key1738, -4), (key1517, -4), (key1509, -4), (key1745, -4), (key1509, 6), (key1505, 6), (key1738, 6), (key1509, 6)]

theorem rawRowCheck13011 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form19 = rawRow13011 := by decide +kernel

def row13011 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

theorem rowCheck13011 : row13011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13011 := by decide +kernel

theorem rowEval13011 (x : Key → ℝ) : Integer.Sparse.eval row13011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck13011, Integer.Sparse.eval_collectBalanced, rawRowCheck13011]

def rawRow13012 : Integer.Sparse Key := [(key1738, -4), (key1509, -4), (key1745, -4), (key1509, -4), (key1745, -4), (key1517, -4), (key1505, 6), (key1738, 6), (key1509, 6), (key1509, 6)]

theorem rawRowCheck13012 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form19 = rawRow13012 := by decide +kernel

def row13012 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

theorem rowCheck13012 : row13012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13012 := by decide +kernel

theorem rowEval13012 (x : Key → ℝ) : Integer.Sparse.eval row13012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form19) x := by
  rw [rowCheck13012, Integer.Sparse.eval_collectBalanced, rawRowCheck13012]

def rawRow13013 : Integer.Sparse Key := [(key1738, -4), (key1745, -4), (key1509, -4), (key1745, -4), (key1509, -4), (key1517, -4), (key1738, 6), (key1505, 6), (key1509, 6), (key1509, 6)]

theorem rawRowCheck13013 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form19 = rawRow13013 := by decide +kernel

def row13013 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

theorem rowCheck13013 : row13013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13013 := by decide +kernel

theorem rowEval13013 (x : Key → ℝ) : Integer.Sparse.eval row13013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck13013, Integer.Sparse.eval_collectBalanced, rawRowCheck13013]

def rawRow13014 : Integer.Sparse Key := [(key1745, -4), (key1509, -4), (key1738, -4), (key1517, -4), (key1745, -4), (key1509, -4), (key1509, 6), (key1738, 6), (key1505, 6), (key1509, 6)]

theorem rawRowCheck13014 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form19 = rawRow13014 := by decide +kernel

def row13014 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

theorem rowCheck13014 : row13014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13014 := by decide +kernel

theorem rowEval13014 (x : Key → ℝ) : Integer.Sparse.eval row13014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck13014, Integer.Sparse.eval_collectBalanced, rawRowCheck13014]

def rawRow13015 : Integer.Sparse Key := [(key1745, -4), (key1738, -4), (key1509, -4), (key1745, -4), (key1517, -4), (key1509, -4), (key1738, 6), (key1509, 6), (key1505, 6), (key1509, 6)]

theorem rawRowCheck13015 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form19 = rawRow13015 := by decide +kernel

def row13015 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

theorem rowCheck13015 : row13015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13015 := by decide +kernel

theorem rowEval13015 (x : Key → ℝ) : Integer.Sparse.eval row13015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck13015, Integer.Sparse.eval_collectBalanced, rawRowCheck13015]

def rawRow13016 : Integer.Sparse Key := [(key1517, -4), (key1745, -4), (key1745, -4), (key1509, -4), (key1509, -4), (key1738, -4), (key1509, 6), (key1509, 6), (key1738, 6), (key1505, 6)]

theorem rawRowCheck13016 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form19 = rawRow13016 := by decide +kernel

def row13016 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

theorem rowCheck13016 : row13016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13016 := by decide +kernel

theorem rowEval13016 (x : Key → ℝ) : Integer.Sparse.eval row13016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck13016, Integer.Sparse.eval_collectBalanced, rawRowCheck13016]

def rawRow13017 : Integer.Sparse Key := [(key1745, -4), (key1517, -4), (key1745, -4), (key1509, -4), (key1738, -4), (key1509, -4), (key1509, 6), (key1738, 6), (key1509, 6), (key1505, 6)]

theorem rawRowCheck13017 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form19 = rawRow13017 := by decide +kernel

def row13017 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

theorem rowCheck13017 : row13017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13017 := by decide +kernel

theorem rowEval13017 (x : Key → ℝ) : Integer.Sparse.eval row13017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck13017, Integer.Sparse.eval_collectBalanced, rawRowCheck13017]

def rawRow13018 : Integer.Sparse Key := [(key1745, -4), (key1745, -4), (key1517, -4), (key1738, -4), (key1509, -4), (key1509, -4), (key1738, 6), (key1509, 6), (key1509, 6), (key1505, 6)]

theorem rawRowCheck13018 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form19 = rawRow13018 := by decide +kernel

def row13018 : Integer.Sparse Key := [(key1505, 6), (key1509, 4), (key1517, -4), (key1738, 2), (key1745, -8)]

theorem rowCheck13018 : row13018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13018 := by decide +kernel

theorem rowEval13018 (x : Key → ℝ) : Integer.Sparse.eval row13018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck13018, Integer.Sparse.eval_collectBalanced, rawRowCheck13018]

def rawRow13019 : Integer.Sparse Key := [(key514, 6), (key514, 6), (key519, 6), (key550, 6), (key519, -24)]

theorem rawRowCheck13019 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form20 = rawRow13019 := by decide +kernel

def row13019 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

theorem rowCheck13019 : row13019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13019 := by decide +kernel

theorem rowEval13019 (x : Key → ℝ) : Integer.Sparse.eval row13019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck13019, Integer.Sparse.eval_collectBalanced, rawRowCheck13019]

def rawRow13020 : Integer.Sparse Key := [(key514, 6), (key519, 6), (key514, 6), (key550, 6), (key519, -24)]

theorem rawRowCheck13020 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form20 = rawRow13020 := by decide +kernel

def row13020 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

theorem rowCheck13020 : row13020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13020 := by decide +kernel

theorem rowEval13020 (x : Key → ℝ) : Integer.Sparse.eval row13020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck13020, Integer.Sparse.eval_collectBalanced, rawRowCheck13020]

def rawRow13021 : Integer.Sparse Key := [(key519, 6), (key514, 6), (key514, 6), (key550, 6), (key519, -24)]

theorem rawRowCheck13021 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form20 = rawRow13021 := by decide +kernel

def row13021 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

theorem rowCheck13021 : row13021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13021 := by decide +kernel

theorem rowEval13021 (x : Key → ℝ) : Integer.Sparse.eval row13021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck13021, Integer.Sparse.eval_collectBalanced, rawRowCheck13021]

def rawRow13022 : Integer.Sparse Key := [(key514, 6), (key514, 6), (key550, 6), (key519, 6), (key519, -24)]

theorem rawRowCheck13022 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form20 = rawRow13022 := by decide +kernel

def row13022 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

theorem rowCheck13022 : row13022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13022 := by decide +kernel

theorem rowEval13022 (x : Key → ℝ) : Integer.Sparse.eval row13022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck13022, Integer.Sparse.eval_collectBalanced, rawRowCheck13022]

def rawRow13023 : Integer.Sparse Key := [(key514, 6), (key550, 6), (key514, 6), (key519, 6), (key519, -24)]

theorem rawRowCheck13023 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form20 = rawRow13023 := by decide +kernel

def row13023 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

theorem rowCheck13023 : row13023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13023 := by decide +kernel

theorem rowEval13023 (x : Key → ℝ) : Integer.Sparse.eval row13023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck13023, Integer.Sparse.eval_collectBalanced, rawRowCheck13023]

def rawRow13024 : Integer.Sparse Key := [(key550, 6), (key514, 6), (key514, 6), (key519, 6), (key519, -24)]

theorem rawRowCheck13024 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form20 = rawRow13024 := by decide +kernel

def row13024 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

theorem rowCheck13024 : row13024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13024 := by decide +kernel

theorem rowEval13024 (x : Key → ℝ) : Integer.Sparse.eval row13024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck13024, Integer.Sparse.eval_collectBalanced, rawRowCheck13024]

def rawRow13025 : Integer.Sparse Key := [(key514, 6), (key519, 6), (key550, 6), (key514, 6), (key519, -24)]

theorem rawRowCheck13025 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form20 = rawRow13025 := by decide +kernel

def row13025 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

theorem rowCheck13025 : row13025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13025 := by decide +kernel

theorem rowEval13025 (x : Key → ℝ) : Integer.Sparse.eval row13025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck13025, Integer.Sparse.eval_collectBalanced, rawRowCheck13025]

def rawRow13026 : Integer.Sparse Key := [(key519, 6), (key514, 6), (key550, 6), (key514, 6), (key519, -24)]

theorem rawRowCheck13026 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form20 = rawRow13026 := by decide +kernel

def row13026 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

theorem rowCheck13026 : row13026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13026 := by decide +kernel

theorem rowEval13026 (x : Key → ℝ) : Integer.Sparse.eval row13026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck13026, Integer.Sparse.eval_collectBalanced, rawRowCheck13026]

def rawRow13027 : Integer.Sparse Key := [(key514, 6), (key550, 6), (key519, 6), (key514, 6), (key519, -24)]

theorem rawRowCheck13027 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form20 = rawRow13027 := by decide +kernel

def row13027 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

theorem rowCheck13027 : row13027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13027 := by decide +kernel

theorem rowEval13027 (x : Key → ℝ) : Integer.Sparse.eval row13027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck13027, Integer.Sparse.eval_collectBalanced, rawRowCheck13027]

def rawRow13028 : Integer.Sparse Key := [(key550, 6), (key514, 6), (key519, 6), (key514, 6), (key519, -24)]

theorem rawRowCheck13028 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form20 = rawRow13028 := by decide +kernel

def row13028 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

theorem rowCheck13028 : row13028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13028 := by decide +kernel

theorem rowEval13028 (x : Key → ℝ) : Integer.Sparse.eval row13028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck13028, Integer.Sparse.eval_collectBalanced, rawRowCheck13028]

def rawRow13029 : Integer.Sparse Key := [(key519, 6), (key550, 6), (key514, 6), (key514, 6), (key519, -24)]

theorem rawRowCheck13029 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form20 = rawRow13029 := by decide +kernel

def row13029 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

theorem rowCheck13029 : row13029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13029 := by decide +kernel

theorem rowEval13029 (x : Key → ℝ) : Integer.Sparse.eval row13029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck13029, Integer.Sparse.eval_collectBalanced, rawRowCheck13029]

def rawRow13030 : Integer.Sparse Key := [(key550, 6), (key519, 6), (key514, 6), (key514, 6), (key519, -24)]

theorem rawRowCheck13030 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form20 = rawRow13030 := by decide +kernel

def row13030 : Integer.Sparse Key := [(key514, 12), (key519, -18), (key550, 6)]

theorem rowCheck13030 : row13030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13030 := by decide +kernel

theorem rowEval13030 (x : Key → ℝ) : Integer.Sparse.eval row13030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck13030, Integer.Sparse.eval_collectBalanced, rawRowCheck13030]

def rawRow13031 : Integer.Sparse Key := [(key514, 6), (key519, 6), (key519, 6), (key550, 6), (key514, -24)]

theorem rawRowCheck13031 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form20 = rawRow13031 := by decide +kernel

def row13031 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

theorem rowCheck13031 : row13031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13031 := by decide +kernel

theorem rowEval13031 (x : Key → ℝ) : Integer.Sparse.eval row13031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck13031, Integer.Sparse.eval_collectBalanced, rawRowCheck13031]

def rawRow13032 : Integer.Sparse Key := [(key519, 6), (key514, 6), (key519, 6), (key550, 6), (key514, -24)]

theorem rawRowCheck13032 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form20 = rawRow13032 := by decide +kernel

def row13032 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

theorem rowCheck13032 : row13032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13032 := by decide +kernel

theorem rowEval13032 (x : Key → ℝ) : Integer.Sparse.eval row13032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck13032, Integer.Sparse.eval_collectBalanced, rawRowCheck13032]

def rawRow13033 : Integer.Sparse Key := [(key519, 6), (key519, 6), (key514, 6), (key550, 6), (key514, -24)]

theorem rawRowCheck13033 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form20 = rawRow13033 := by decide +kernel

def row13033 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

theorem rowCheck13033 : row13033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13033 := by decide +kernel

theorem rowEval13033 (x : Key → ℝ) : Integer.Sparse.eval row13033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck13033, Integer.Sparse.eval_collectBalanced, rawRowCheck13033]

def rawRow13034 : Integer.Sparse Key := [(key514, 6), (key519, 6), (key550, 6), (key519, 6), (key514, -24)]

theorem rawRowCheck13034 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form20 = rawRow13034 := by decide +kernel

def row13034 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

theorem rowCheck13034 : row13034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13034 := by decide +kernel

theorem rowEval13034 (x : Key → ℝ) : Integer.Sparse.eval row13034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck13034, Integer.Sparse.eval_collectBalanced, rawRowCheck13034]

def rawRow13035 : Integer.Sparse Key := [(key519, 6), (key514, 6), (key550, 6), (key519, 6), (key514, -24)]

theorem rawRowCheck13035 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form20 = rawRow13035 := by decide +kernel

def row13035 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

theorem rowCheck13035 : row13035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13035 := by decide +kernel

theorem rowEval13035 (x : Key → ℝ) : Integer.Sparse.eval row13035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck13035, Integer.Sparse.eval_collectBalanced, rawRowCheck13035]

def rawRow13036 : Integer.Sparse Key := [(key514, 6), (key550, 6), (key519, 6), (key519, 6), (key514, -24)]

theorem rawRowCheck13036 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form20 = rawRow13036 := by decide +kernel

def row13036 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

theorem rowCheck13036 : row13036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13036 := by decide +kernel

theorem rowEval13036 (x : Key → ℝ) : Integer.Sparse.eval row13036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form20) x := by
  rw [rowCheck13036, Integer.Sparse.eval_collectBalanced, rawRowCheck13036]

def rawRow13037 : Integer.Sparse Key := [(key550, 6), (key514, 6), (key519, 6), (key519, 6), (key514, -24)]

theorem rawRowCheck13037 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form20 = rawRow13037 := by decide +kernel

def row13037 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

theorem rowCheck13037 : row13037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13037 := by decide +kernel

theorem rowEval13037 (x : Key → ℝ) : Integer.Sparse.eval row13037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck13037, Integer.Sparse.eval_collectBalanced, rawRowCheck13037]

def rawRow13038 : Integer.Sparse Key := [(key519, 6), (key550, 6), (key514, 6), (key519, 6), (key514, -24)]

theorem rawRowCheck13038 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form20 = rawRow13038 := by decide +kernel

def row13038 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

theorem rowCheck13038 : row13038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13038 := by decide +kernel

theorem rowEval13038 (x : Key → ℝ) : Integer.Sparse.eval row13038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck13038, Integer.Sparse.eval_collectBalanced, rawRowCheck13038]

def rawRow13039 : Integer.Sparse Key := [(key550, 6), (key519, 6), (key514, 6), (key519, 6), (key514, -24)]

theorem rawRowCheck13039 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form20 = rawRow13039 := by decide +kernel

def row13039 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

theorem rowCheck13039 : row13039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13039 := by decide +kernel

theorem rowEval13039 (x : Key → ℝ) : Integer.Sparse.eval row13039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck13039, Integer.Sparse.eval_collectBalanced, rawRowCheck13039]

def rawRow13040 : Integer.Sparse Key := [(key519, 6), (key519, 6), (key550, 6), (key514, 6), (key514, -24)]

theorem rawRowCheck13040 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form20 = rawRow13040 := by decide +kernel

def row13040 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

theorem rowCheck13040 : row13040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13040 := by decide +kernel

theorem rowEval13040 (x : Key → ℝ) : Integer.Sparse.eval row13040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck13040, Integer.Sparse.eval_collectBalanced, rawRowCheck13040]

def rawRow13041 : Integer.Sparse Key := [(key519, 6), (key550, 6), (key519, 6), (key514, 6), (key514, -24)]

theorem rawRowCheck13041 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form20 = rawRow13041 := by decide +kernel

def row13041 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

theorem rowCheck13041 : row13041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13041 := by decide +kernel

theorem rowEval13041 (x : Key → ℝ) : Integer.Sparse.eval row13041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck13041, Integer.Sparse.eval_collectBalanced, rawRowCheck13041]

def rawRow13042 : Integer.Sparse Key := [(key550, 6), (key519, 6), (key519, 6), (key514, 6), (key514, -24)]

theorem rawRowCheck13042 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form20 = rawRow13042 := by decide +kernel

def row13042 : Integer.Sparse Key := [(key514, -18), (key519, 12), (key550, 6)]

theorem rowCheck13042 : row13042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13042 := by decide +kernel

theorem rowEval13042 (x : Key → ℝ) : Integer.Sparse.eval row13042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck13042, Integer.Sparse.eval_collectBalanced, rawRowCheck13042]

def rawRow13043 : Integer.Sparse Key := [(key1367, 1), (key1367, 1), (key1376, 1), (key1376, 1), (key1380, 1), (key1380, 1), (key1493, 1), (key1493, 1), (key1515, 1), (key1515, 1), (key1520, 1), (key1520, 1), (key1725, 1), (key1725, 1), (key1743, 1), (key1743, 1), (key1759, 1), (key1759, 1), (key1871, 1), (key1871, 1), (key1881, 1), (key1881, 1), (key1889, 1), (key1889, 1), (key1371, -2), (key1380, -2), (key1380, -2), (key1497, -2), (key1520, -2), (key1520, -2), (key1729, -2), (key1729, -2), (key1748, -2), (key1748, -2), (key1759, -2), (key1759, -2)]

theorem rawRowCheck13043 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form21 = rawRow13043 := by decide +kernel

def row13043 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

theorem rowCheck13043 : row13043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13043 := by decide +kernel

theorem rowEval13043 (x : Key → ℝ) : Integer.Sparse.eval row13043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck13043, Integer.Sparse.eval_collectBalanced, rawRowCheck13043]

def rawRow13044 : Integer.Sparse Key := [(key1376, 1), (key1380, 1), (key1367, 1), (key1380, 1), (key1367, 1), (key1376, 1), (key1515, 1), (key1520, 1), (key1493, 1), (key1520, 1), (key1493, 1), (key1515, 1), (key1743, 1), (key1759, 1), (key1725, 1), (key1759, 1), (key1725, 1), (key1743, 1), (key1881, 1), (key1889, 1), (key1871, 1), (key1889, 1), (key1871, 1), (key1881, 1), (key1380, -2), (key1371, -2), (key1380, -2), (key1520, -2), (key1497, -2), (key1520, -2), (key1748, -2), (key1759, -2), (key1729, -2), (key1759, -2), (key1729, -2), (key1748, -2)]

theorem rawRowCheck13044 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form21 = rawRow13044 := by decide +kernel

def row13044 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

theorem rowCheck13044 : row13044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13044 := by decide +kernel

theorem rowEval13044 (x : Key → ℝ) : Integer.Sparse.eval row13044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck13044, Integer.Sparse.eval_collectBalanced, rawRowCheck13044]

def rawRow13045 : Integer.Sparse Key := [(key1380, 1), (key1376, 1), (key1380, 1), (key1367, 1), (key1376, 1), (key1367, 1), (key1520, 1), (key1515, 1), (key1520, 1), (key1493, 1), (key1515, 1), (key1493, 1), (key1759, 1), (key1743, 1), (key1759, 1), (key1725, 1), (key1743, 1), (key1725, 1), (key1889, 1), (key1881, 1), (key1889, 1), (key1871, 1), (key1881, 1), (key1871, 1), (key1380, -2), (key1380, -2), (key1371, -2), (key1520, -2), (key1520, -2), (key1497, -2), (key1759, -2), (key1748, -2), (key1759, -2), (key1729, -2), (key1748, -2), (key1729, -2)]

theorem rawRowCheck13045 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form21 = rawRow13045 := by decide +kernel

def row13045 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

theorem rowCheck13045 : row13045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13045 := by decide +kernel

theorem rowEval13045 (x : Key → ℝ) : Integer.Sparse.eval row13045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck13045, Integer.Sparse.eval_collectBalanced, rawRowCheck13045]

def rawRow13046 : Integer.Sparse Key := [(key1493, 1), (key1493, 1), (key1725, 1), (key1725, 1), (key1871, 1), (key1871, 1), (key1367, 1), (key1367, 1), (key1743, 1), (key1743, 1), (key1881, 1), (key1881, 1), (key1376, 1), (key1376, 1), (key1515, 1), (key1515, 1), (key1889, 1), (key1889, 1), (key1380, 1), (key1380, 1), (key1520, 1), (key1520, 1), (key1759, 1), (key1759, 1), (key1497, -2), (key1729, -2), (key1729, -2), (key1371, -2), (key1748, -2), (key1748, -2), (key1380, -2), (key1380, -2), (key1520, -2), (key1520, -2), (key1759, -2), (key1759, -2)]

theorem rawRowCheck13046 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form21 = rawRow13046 := by decide +kernel

def row13046 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

theorem rowCheck13046 : row13046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13046 := by decide +kernel

theorem rowEval13046 (x : Key → ℝ) : Integer.Sparse.eval row13046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck13046, Integer.Sparse.eval_collectBalanced, rawRowCheck13046]

def rawRow13047 : Integer.Sparse Key := [(key1725, 1), (key1871, 1), (key1493, 1), (key1871, 1), (key1493, 1), (key1725, 1), (key1743, 1), (key1881, 1), (key1367, 1), (key1881, 1), (key1367, 1), (key1743, 1), (key1515, 1), (key1889, 1), (key1376, 1), (key1889, 1), (key1376, 1), (key1515, 1), (key1520, 1), (key1759, 1), (key1380, 1), (key1759, 1), (key1380, 1), (key1520, 1), (key1729, -2), (key1497, -2), (key1729, -2), (key1748, -2), (key1371, -2), (key1748, -2), (key1520, -2), (key1759, -2), (key1380, -2), (key1759, -2), (key1380, -2), (key1520, -2)]

theorem rawRowCheck13047 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form21 = rawRow13047 := by decide +kernel

def row13047 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

theorem rowCheck13047 : row13047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13047 := by decide +kernel

theorem rowEval13047 (x : Key → ℝ) : Integer.Sparse.eval row13047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck13047, Integer.Sparse.eval_collectBalanced, rawRowCheck13047]

def rawRow13048 : Integer.Sparse Key := [(key1871, 1), (key1725, 1), (key1871, 1), (key1493, 1), (key1725, 1), (key1493, 1), (key1881, 1), (key1743, 1), (key1881, 1), (key1367, 1), (key1743, 1), (key1367, 1), (key1889, 1), (key1515, 1), (key1889, 1), (key1376, 1), (key1515, 1), (key1376, 1), (key1759, 1), (key1520, 1), (key1759, 1), (key1380, 1), (key1520, 1), (key1380, 1), (key1729, -2), (key1729, -2), (key1497, -2), (key1748, -2), (key1748, -2), (key1371, -2), (key1759, -2), (key1520, -2), (key1759, -2), (key1380, -2), (key1520, -2), (key1380, -2)]

theorem rawRowCheck13048 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form21 = rawRow13048 := by decide +kernel

def row13048 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

theorem rowCheck13048 : row13048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13048 := by decide +kernel

theorem rowEval13048 (x : Key → ℝ) : Integer.Sparse.eval row13048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck13048, Integer.Sparse.eval_collectBalanced, rawRowCheck13048]

def rawRow13049 : Integer.Sparse Key := [(key1515, 1), (key1520, 1), (key1743, 1), (key1759, 1), (key1881, 1), (key1889, 1), (key1376, 1), (key1380, 1), (key1725, 1), (key1759, 1), (key1871, 1), (key1889, 1), (key1367, 1), (key1380, 1), (key1493, 1), (key1520, 1), (key1871, 1), (key1881, 1), (key1367, 1), (key1376, 1), (key1493, 1), (key1515, 1), (key1725, 1), (key1743, 1), (key1520, -2), (key1748, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1759, -2), (key1371, -2), (key1380, -2), (key1497, -2), (key1520, -2), (key1729, -2), (key1748, -2)]

theorem rawRowCheck13049 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form21 = rawRow13049 := by decide +kernel

def row13049 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

theorem rowCheck13049 : row13049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13049 := by decide +kernel

theorem rowEval13049 (x : Key → ℝ) : Integer.Sparse.eval row13049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck13049, Integer.Sparse.eval_collectBalanced, rawRowCheck13049]

def rawRow13050 : Integer.Sparse Key := [(key1520, 1), (key1515, 1), (key1759, 1), (key1743, 1), (key1889, 1), (key1881, 1), (key1380, 1), (key1376, 1), (key1759, 1), (key1725, 1), (key1889, 1), (key1871, 1), (key1380, 1), (key1367, 1), (key1520, 1), (key1493, 1), (key1881, 1), (key1871, 1), (key1376, 1), (key1367, 1), (key1515, 1), (key1493, 1), (key1743, 1), (key1725, 1), (key1520, -2), (key1759, -2), (key1748, -2), (key1380, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1371, -2), (key1520, -2), (key1497, -2), (key1748, -2), (key1729, -2)]

theorem rawRowCheck13050 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form21 = rawRow13050 := by decide +kernel

def row13050 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

theorem rowCheck13050 : row13050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13050 := by decide +kernel

theorem rowEval13050 (x : Key → ℝ) : Integer.Sparse.eval row13050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck13050, Integer.Sparse.eval_collectBalanced, rawRowCheck13050]

def rawRow13051 : Integer.Sparse Key := [(key1743, 1), (key1881, 1), (key1515, 1), (key1889, 1), (key1520, 1), (key1759, 1), (key1725, 1), (key1871, 1), (key1376, 1), (key1889, 1), (key1380, 1), (key1759, 1), (key1493, 1), (key1871, 1), (key1367, 1), (key1881, 1), (key1380, 1), (key1520, 1), (key1493, 1), (key1725, 1), (key1367, 1), (key1743, 1), (key1376, 1), (key1515, 1), (key1748, -2), (key1520, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1759, -2), (key1497, -2), (key1729, -2), (key1371, -2), (key1748, -2), (key1380, -2), (key1520, -2)]

theorem rawRowCheck13051 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form21 = rawRow13051 := by decide +kernel

def row13051 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

theorem rowCheck13051 : row13051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13051 := by decide +kernel

theorem rowEval13051 (x : Key → ℝ) : Integer.Sparse.eval row13051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck13051, Integer.Sparse.eval_collectBalanced, rawRowCheck13051]

def rawRow13052 : Integer.Sparse Key := [(key1881, 1), (key1743, 1), (key1889, 1), (key1515, 1), (key1759, 1), (key1520, 1), (key1871, 1), (key1725, 1), (key1889, 1), (key1376, 1), (key1759, 1), (key1380, 1), (key1871, 1), (key1493, 1), (key1881, 1), (key1367, 1), (key1520, 1), (key1380, 1), (key1725, 1), (key1493, 1), (key1743, 1), (key1367, 1), (key1515, 1), (key1376, 1), (key1748, -2), (key1759, -2), (key1520, -2), (key1729, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1497, -2), (key1748, -2), (key1371, -2), (key1520, -2), (key1380, -2)]

theorem rawRowCheck13052 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form21 = rawRow13052 := by decide +kernel

def row13052 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

theorem rowCheck13052 : row13052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13052 := by decide +kernel

theorem rowEval13052 (x : Key → ℝ) : Integer.Sparse.eval row13052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck13052, Integer.Sparse.eval_collectBalanced, rawRowCheck13052]

def rawRow13053 : Integer.Sparse Key := [(key1759, 1), (key1889, 1), (key1520, 1), (key1881, 1), (key1515, 1), (key1743, 1), (key1759, 1), (key1889, 1), (key1380, 1), (key1871, 1), (key1376, 1), (key1725, 1), (key1520, 1), (key1881, 1), (key1380, 1), (key1871, 1), (key1367, 1), (key1493, 1), (key1515, 1), (key1743, 1), (key1376, 1), (key1725, 1), (key1367, 1), (key1493, 1), (key1759, -2), (key1520, -2), (key1748, -2), (key1759, -2), (key1380, -2), (key1729, -2), (key1520, -2), (key1748, -2), (key1380, -2), (key1729, -2), (key1371, -2), (key1497, -2)]

theorem rawRowCheck13053 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form21 = rawRow13053 := by decide +kernel

def row13053 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

theorem rowCheck13053 : row13053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13053 := by decide +kernel

theorem rowEval13053 (x : Key → ℝ) : Integer.Sparse.eval row13053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck13053, Integer.Sparse.eval_collectBalanced, rawRowCheck13053]

def rawRow13054 : Integer.Sparse Key := [(key1889, 1), (key1759, 1), (key1881, 1), (key1520, 1), (key1743, 1), (key1515, 1), (key1889, 1), (key1759, 1), (key1871, 1), (key1380, 1), (key1725, 1), (key1376, 1), (key1881, 1), (key1520, 1), (key1871, 1), (key1380, 1), (key1493, 1), (key1367, 1), (key1743, 1), (key1515, 1), (key1725, 1), (key1376, 1), (key1493, 1), (key1367, 1), (key1759, -2), (key1748, -2), (key1520, -2), (key1759, -2), (key1729, -2), (key1380, -2), (key1748, -2), (key1520, -2), (key1729, -2), (key1380, -2), (key1497, -2), (key1371, -2)]

theorem rawRowCheck13054 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form21 = rawRow13054 := by decide +kernel

def row13054 : Integer.Sparse Key := [(key1367, 2), (key1371, -2), (key1376, 2), (key1380, -2), (key1493, 2), (key1497, -2), (key1515, 2), (key1520, -2), (key1725, 2), (key1729, -4), (key1743, 2), (key1748, -4), (key1759, -2), (key1871, 2), (key1881, 2), (key1889, 2)]

theorem rowCheck13054 : row13054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13054 := by decide +kernel

theorem rowEval13054 (x : Key → ℝ) : Integer.Sparse.eval row13054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck13054, Integer.Sparse.eval_collectBalanced, rawRowCheck13054]

def rawRow13055 : Integer.Sparse Key := [(key1367, 1), (key1371, 1), (key1367, 1), (key1380, 1), (key1371, 1), (key1380, 1), (key1493, 1), (key1497, 1), (key1493, 1), (key1520, 1), (key1497, 1), (key1520, 1), (key1719, 1), (key1729, 1), (key1719, 1), (key1748, 1), (key1729, 1), (key1748, 1), (key1866, 1), (key1871, 1), (key1866, 1), (key1881, 1), (key1871, 1), (key1881, 1), (key1367, -2), (key1367, -2), (key1376, -2), (key1493, -2), (key1493, -2), (key1515, -2), (key1719, -2), (key1725, -2), (key1719, -2), (key1743, -2), (key1725, -2), (key1743, -2)]

theorem rawRowCheck13055 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form21 = rawRow13055 := by decide +kernel

def row13055 : Integer.Sparse Key := [(key1367, -2), (key1371, 2), (key1376, -2), (key1380, 2), (key1493, -2), (key1497, 2), (key1515, -2), (key1520, 2), (key1719, -2), (key1725, -4), (key1729, 2), (key1743, -4), (key1748, 2), (key1866, 2), (key1871, 2), (key1881, 2)]

theorem rowCheck13055 : row13055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13055 := by decide +kernel

theorem rowEval13055 (x : Key → ℝ) : Integer.Sparse.eval row13055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form21) x := by
  rw [rowCheck13055, Integer.Sparse.eval_collectBalanced, rawRowCheck13055]

end MUB6.Certificate.GramRows

end OAI
