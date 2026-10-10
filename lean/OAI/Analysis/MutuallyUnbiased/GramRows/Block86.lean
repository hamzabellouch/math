import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block0
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow7936 : Integer.Sparse Key := [(key2698, -2), (key2704, -2), (key2724, -2), (key2663, -2), (key2669, -2), (key2698, -2), (key2752, -2), (key2724, -2), (key2757, -2), (key2669, -2), (key2704, -2), (key2752, -2), (key2801, 2), (key2807, 2), (key2827, 2), (key2608, 2), (key2614, 2), (key2801, 2), (key2827, 2), (key3011, 2), (key3016, 2), (key2614, 2), (key2807, 2), (key2827, 2)]

theorem rawRowCheck7936 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form7 = rawRow7936 := by decide +kernel

def row7936 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 6), (key3011, 2), (key3016, 2)]

theorem rowCheck7936 : row7936 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7936 := by decide +kernel

theorem rowEval7936 (x : Key → ℝ) : Integer.Sparse.eval row7936 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck7936, Integer.Sparse.eval_collectBalanced, rawRowCheck7936]

def rawRow7937 : Integer.Sparse Key := [(key2704, -2), (key2698, -2), (key2724, -2), (key2669, -2), (key2663, -2), (key2752, -2), (key2698, -2), (key2757, -2), (key2724, -2), (key2669, -2), (key2752, -2), (key2704, -2), (key2807, 2), (key2801, 2), (key2827, 2), (key2614, 2), (key2608, 2), (key2827, 2), (key2801, 2), (key3016, 2), (key3011, 2), (key2614, 2), (key2827, 2), (key2807, 2)]

theorem rawRowCheck7937 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form7 = rawRow7937 := by decide +kernel

def row7937 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 6), (key3011, 2), (key3016, 2)]

theorem rowCheck7937 : row7937 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7937 := by decide +kernel

theorem rowEval7937 (x : Key → ℝ) : Integer.Sparse.eval row7937 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7937, Integer.Sparse.eval_collectBalanced, rawRowCheck7937]

def rawRow7938 : Integer.Sparse Key := [(key2698, -2), (key2724, -2), (key2704, -2), (key2698, -2), (key2724, -2), (key2663, -2), (key2757, -2), (key2669, -2), (key2752, -2), (key2704, -2), (key2669, -2), (key2752, -2), (key2801, 2), (key2827, 2), (key2807, 2), (key2801, 2), (key2827, 2), (key2608, 2), (key3016, 2), (key2614, 2), (key2827, 2), (key2807, 2), (key2614, 2), (key2827, 2)]

theorem rawRowCheck7938 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form7 = rawRow7938 := by decide +kernel

def row7938 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 8), (key3016, 2)]

theorem rowCheck7938 : row7938 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7938 := by decide +kernel

theorem rowEval7938 (x : Key → ℝ) : Integer.Sparse.eval row7938 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form7) x := by
  rw [rowCheck7938, Integer.Sparse.eval_collectBalanced, rawRowCheck7938]

def rawRow7939 : Integer.Sparse Key := [(key2724, -2), (key2698, -2), (key2704, -2), (key2724, -2), (key2698, -2), (key2757, -2), (key2663, -2), (key2752, -2), (key2669, -2), (key2704, -2), (key2752, -2), (key2669, -2), (key2827, 2), (key2801, 2), (key2807, 2), (key2827, 2), (key2801, 2), (key3016, 2), (key2608, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2827, 2), (key2614, 2)]

theorem rawRowCheck7939 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form7 = rawRow7939 := by decide +kernel

def row7939 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 8), (key3016, 2)]

theorem rowCheck7939 : row7939 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7939 := by decide +kernel

theorem rowEval7939 (x : Key → ℝ) : Integer.Sparse.eval row7939 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck7939, Integer.Sparse.eval_collectBalanced, rawRowCheck7939]

def rawRow7940 : Integer.Sparse Key := [(key2704, -2), (key2724, -2), (key2698, -2), (key2752, -2), (key2757, -2), (key2669, -2), (key2724, -2), (key2663, -2), (key2698, -2), (key2752, -2), (key2669, -2), (key2704, -2), (key2807, 2), (key2827, 2), (key2801, 2), (key3011, 2), (key3016, 2), (key2614, 2), (key2827, 2), (key2608, 2), (key2801, 2), (key2827, 2), (key2614, 2), (key2807, 2)]

theorem rawRowCheck7940 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form7 = rawRow7940 := by decide +kernel

def row7940 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 6), (key3011, 2), (key3016, 2)]

theorem rowCheck7940 : row7940 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7940 := by decide +kernel

theorem rowEval7940 (x : Key → ℝ) : Integer.Sparse.eval row7940 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7940, Integer.Sparse.eval_collectBalanced, rawRowCheck7940]

def rawRow7941 : Integer.Sparse Key := [(key2724, -2), (key2704, -2), (key2698, -2), (key2757, -2), (key2752, -2), (key2724, -2), (key2669, -2), (key2698, -2), (key2663, -2), (key2752, -2), (key2704, -2), (key2669, -2), (key2827, 2), (key2807, 2), (key2801, 2), (key3016, 2), (key3011, 2), (key2827, 2), (key2614, 2), (key2801, 2), (key2608, 2), (key2827, 2), (key2807, 2), (key2614, 2)]

theorem rawRowCheck7941 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form7 = rawRow7941 := by decide +kernel

def row7941 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 6), (key3011, 2), (key3016, 2)]

theorem rowCheck7941 : row7941 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7941 := by decide +kernel

theorem rowEval7941 (x : Key → ℝ) : Integer.Sparse.eval row7941 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck7941, Integer.Sparse.eval_collectBalanced, rawRowCheck7941]

def rawRow7942 : Integer.Sparse Key := [(key2752, -2), (key2752, -2), (key2757, -2), (key2669, -2), (key2669, -2), (key2704, -2), (key2704, -2), (key2724, -2), (key2724, -2), (key2663, -2), (key2698, -2), (key2698, -2), (key3011, 2), (key3011, 2), (key3016, 2), (key2614, 2), (key2614, 2), (key2807, 2), (key2807, 2), (key2827, 2), (key2827, 2), (key2608, 2), (key2801, 2), (key2801, 2)]

theorem rawRowCheck7942 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form7 = rawRow7942 := by decide +kernel

def row7942 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 4), (key3011, 4), (key3016, 2)]

theorem rowCheck7942 : row7942 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7942 := by decide +kernel

theorem rowEval7942 (x : Key → ℝ) : Integer.Sparse.eval row7942 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7942, Integer.Sparse.eval_collectBalanced, rawRowCheck7942]

def rawRow7943 : Integer.Sparse Key := [(key2752, -2), (key2757, -2), (key2752, -2), (key2704, -2), (key2724, -2), (key2669, -2), (key2724, -2), (key2669, -2), (key2704, -2), (key2698, -2), (key2663, -2), (key2698, -2), (key3011, 2), (key3016, 2), (key3011, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2801, 2), (key2608, 2), (key2801, 2)]

theorem rawRowCheck7943 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form7 = rawRow7943 := by decide +kernel

def row7943 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 4), (key3011, 4), (key3016, 2)]

theorem rowCheck7943 : row7943 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7943 := by decide +kernel

theorem rowEval7943 (x : Key → ℝ) : Integer.Sparse.eval row7943 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck7943, Integer.Sparse.eval_collectBalanced, rawRowCheck7943]

def rawRow7944 : Integer.Sparse Key := [(key2757, -2), (key2752, -2), (key2752, -2), (key2724, -2), (key2704, -2), (key2724, -2), (key2669, -2), (key2704, -2), (key2669, -2), (key2698, -2), (key2698, -2), (key2663, -2), (key3016, 2), (key3011, 2), (key3011, 2), (key2827, 2), (key2807, 2), (key2827, 2), (key2614, 2), (key2807, 2), (key2614, 2), (key2801, 2), (key2801, 2), (key2608, 2)]

theorem rawRowCheck7944 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form7 = rawRow7944 := by decide +kernel

def row7944 : Integer.Sparse Key := [(key2608, 2), (key2614, 4), (key2663, -2), (key2669, -4), (key2698, -4), (key2704, -4), (key2724, -4), (key2752, -4), (key2757, -2), (key2801, 4), (key2807, 4), (key2827, 4), (key3011, 4), (key3016, 2)]

theorem rowCheck7944 : row7944 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7944 := by decide +kernel

theorem rowEval7944 (x : Key → ℝ) : Integer.Sparse.eval row7944 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck7944, Integer.Sparse.eval_collectBalanced, rawRowCheck7944]

def rawRow7945 : Integer.Sparse Key := [(key1256, 2), (key1256, 2), (key1261, 2), (key1609, 2), (key1609, 2), (key1642, 2), (key1806, 2), (key1809, 2), (key1806, 2), (key1832, 2), (key1809, 2), (key1832, 2), (key1265, -2), (key1268, -2), (key1268, -2), (key1648, -2), (key1651, -2), (key1648, -2), (key1674, -2), (key1651, -2), (key1674, -2), (key1837, -2), (key1837, -2), (key1848, -2)]

theorem rawRowCheck7945 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form0 = rawRow7945 := by decide +kernel

def row7945 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

theorem rowCheck7945 : row7945 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7945 := by decide +kernel

theorem rowEval7945 (x : Key → ℝ) : Integer.Sparse.eval row7945 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7945, Integer.Sparse.eval_collectBalanced, rawRowCheck7945]

def rawRow7946 : Integer.Sparse Key := [(key1256, 2), (key1261, 2), (key1256, 2), (key1609, 2), (key1642, 2), (key1609, 2), (key1809, 2), (key1806, 2), (key1832, 2), (key1806, 2), (key1832, 2), (key1809, 2), (key1268, -2), (key1265, -2), (key1268, -2), (key1651, -2), (key1648, -2), (key1674, -2), (key1648, -2), (key1674, -2), (key1651, -2), (key1837, -2), (key1848, -2), (key1837, -2)]

theorem rawRowCheck7946 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form0 = rawRow7946 := by decide +kernel

def row7946 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

theorem rowCheck7946 : row7946 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7946 := by decide +kernel

theorem rowEval7946 (x : Key → ℝ) : Integer.Sparse.eval row7946 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7946, Integer.Sparse.eval_collectBalanced, rawRowCheck7946]

def rawRow7947 : Integer.Sparse Key := [(key1261, 2), (key1256, 2), (key1256, 2), (key1642, 2), (key1609, 2), (key1609, 2), (key1832, 2), (key1832, 2), (key1809, 2), (key1809, 2), (key1806, 2), (key1806, 2), (key1268, -2), (key1268, -2), (key1265, -2), (key1674, -2), (key1674, -2), (key1651, -2), (key1651, -2), (key1648, -2), (key1648, -2), (key1848, -2), (key1837, -2), (key1837, -2)]

theorem rawRowCheck7947 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form0 = rawRow7947 := by decide +kernel

def row7947 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

theorem rowCheck7947 : row7947 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7947 := by decide +kernel

theorem rowEval7947 (x : Key → ℝ) : Integer.Sparse.eval row7947 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7947, Integer.Sparse.eval_collectBalanced, rawRowCheck7947]

def rawRow7948 : Integer.Sparse Key := [(key1609, 2), (key1806, 2), (key1809, 2), (key1256, 2), (key1806, 2), (key1832, 2), (key1256, 2), (key1261, 2), (key1609, 2), (key1642, 2), (key1809, 2), (key1832, 2), (key1648, -2), (key1651, -2), (key1837, -2), (key1265, -2), (key1268, -2), (key1648, -2), (key1674, -2), (key1837, -2), (key1848, -2), (key1268, -2), (key1651, -2), (key1674, -2)]

theorem rawRowCheck7948 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form0 = rawRow7948 := by decide +kernel

def row7948 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

theorem rowCheck7948 : row7948 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7948 := by decide +kernel

theorem rowEval7948 (x : Key → ℝ) : Integer.Sparse.eval row7948 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7948, Integer.Sparse.eval_collectBalanced, rawRowCheck7948]

def rawRow7949 : Integer.Sparse Key := [(key1609, 2), (key1809, 2), (key1806, 2), (key1256, 2), (key1832, 2), (key1806, 2), (key1261, 2), (key1256, 2), (key1642, 2), (key1609, 2), (key1832, 2), (key1809, 2), (key1651, -2), (key1648, -2), (key1837, -2), (key1268, -2), (key1265, -2), (key1674, -2), (key1648, -2), (key1848, -2), (key1837, -2), (key1268, -2), (key1674, -2), (key1651, -2)]

theorem rawRowCheck7949 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form0 = rawRow7949 := by decide +kernel

def row7949 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

theorem rowCheck7949 : row7949 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7949 := by decide +kernel

theorem rowEval7949 (x : Key → ℝ) : Integer.Sparse.eval row7949 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7949, Integer.Sparse.eval_collectBalanced, rawRowCheck7949]

def rawRow7950 : Integer.Sparse Key := [(key1806, 2), (key1609, 2), (key1809, 2), (key1806, 2), (key1256, 2), (key1832, 2), (key1609, 2), (key1809, 2), (key1256, 2), (key1832, 2), (key1261, 2), (key1642, 2), (key1648, -2), (key1837, -2), (key1651, -2), (key1648, -2), (key1837, -2), (key1265, -2), (key1848, -2), (key1268, -2), (key1674, -2), (key1651, -2), (key1268, -2), (key1674, -2)]

theorem rawRowCheck7950 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form0 = rawRow7950 := by decide +kernel

def row7950 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

theorem rowCheck7950 : row7950 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7950 := by decide +kernel

theorem rowEval7950 (x : Key → ℝ) : Integer.Sparse.eval row7950 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7950, Integer.Sparse.eval_collectBalanced, rawRowCheck7950]

def rawRow7951 : Integer.Sparse Key := [(key1806, 2), (key1809, 2), (key1609, 2), (key1806, 2), (key1832, 2), (key1256, 2), (key1809, 2), (key1609, 2), (key1832, 2), (key1256, 2), (key1642, 2), (key1261, 2), (key1837, -2), (key1648, -2), (key1651, -2), (key1837, -2), (key1648, -2), (key1848, -2), (key1265, -2), (key1674, -2), (key1268, -2), (key1651, -2), (key1674, -2), (key1268, -2)]

theorem rawRowCheck7951 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form0 = rawRow7951 := by decide +kernel

def row7951 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

theorem rowCheck7951 : row7951 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7951 := by decide +kernel

theorem rowEval7951 (x : Key → ℝ) : Integer.Sparse.eval row7951 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7951, Integer.Sparse.eval_collectBalanced, rawRowCheck7951]

def rawRow7952 : Integer.Sparse Key := [(key1809, 2), (key1609, 2), (key1806, 2), (key1832, 2), (key1256, 2), (key1806, 2), (key1642, 2), (key1832, 2), (key1261, 2), (key1809, 2), (key1256, 2), (key1609, 2), (key1651, -2), (key1837, -2), (key1648, -2), (key1674, -2), (key1848, -2), (key1268, -2), (key1837, -2), (key1265, -2), (key1648, -2), (key1674, -2), (key1268, -2), (key1651, -2)]

theorem rawRowCheck7952 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form0 = rawRow7952 := by decide +kernel

def row7952 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

theorem rowCheck7952 : row7952 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7952 := by decide +kernel

theorem rowEval7952 (x : Key → ℝ) : Integer.Sparse.eval row7952 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7952, Integer.Sparse.eval_collectBalanced, rawRowCheck7952]

def rawRow7953 : Integer.Sparse Key := [(key1809, 2), (key1806, 2), (key1609, 2), (key1832, 2), (key1806, 2), (key1256, 2), (key1832, 2), (key1642, 2), (key1809, 2), (key1261, 2), (key1609, 2), (key1256, 2), (key1837, -2), (key1651, -2), (key1648, -2), (key1848, -2), (key1674, -2), (key1837, -2), (key1268, -2), (key1648, -2), (key1265, -2), (key1674, -2), (key1651, -2), (key1268, -2)]

theorem rawRowCheck7953 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form0 = rawRow7953 := by decide +kernel

def row7953 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

theorem rowCheck7953 : row7953 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7953 := by decide +kernel

theorem rowEval7953 (x : Key → ℝ) : Integer.Sparse.eval row7953 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7953, Integer.Sparse.eval_collectBalanced, rawRowCheck7953]

def rawRow7954 : Integer.Sparse Key := [(key1642, 2), (key1832, 2), (key1832, 2), (key1261, 2), (key1809, 2), (key1809, 2), (key1256, 2), (key1256, 2), (key1609, 2), (key1609, 2), (key1806, 2), (key1806, 2), (key1674, -2), (key1674, -2), (key1848, -2), (key1268, -2), (key1268, -2), (key1651, -2), (key1651, -2), (key1837, -2), (key1837, -2), (key1265, -2), (key1648, -2), (key1648, -2)]

theorem rawRowCheck7954 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form0 = rawRow7954 := by decide +kernel

def row7954 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

theorem rowCheck7954 : row7954 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7954 := by decide +kernel

theorem rowEval7954 (x : Key → ℝ) : Integer.Sparse.eval row7954 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7954, Integer.Sparse.eval_collectBalanced, rawRowCheck7954]

def rawRow7955 : Integer.Sparse Key := [(key1832, 2), (key1642, 2), (key1832, 2), (key1809, 2), (key1261, 2), (key1809, 2), (key1609, 2), (key1806, 2), (key1256, 2), (key1806, 2), (key1256, 2), (key1609, 2), (key1674, -2), (key1848, -2), (key1674, -2), (key1651, -2), (key1837, -2), (key1268, -2), (key1837, -2), (key1268, -2), (key1651, -2), (key1648, -2), (key1265, -2), (key1648, -2)]

theorem rawRowCheck7955 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form0 = rawRow7955 := by decide +kernel

def row7955 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

theorem rowCheck7955 : row7955 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7955 := by decide +kernel

theorem rowEval7955 (x : Key → ℝ) : Integer.Sparse.eval row7955 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7955, Integer.Sparse.eval_collectBalanced, rawRowCheck7955]

def rawRow7956 : Integer.Sparse Key := [(key1832, 2), (key1832, 2), (key1642, 2), (key1809, 2), (key1809, 2), (key1261, 2), (key1806, 2), (key1609, 2), (key1806, 2), (key1256, 2), (key1609, 2), (key1256, 2), (key1848, -2), (key1674, -2), (key1674, -2), (key1837, -2), (key1651, -2), (key1837, -2), (key1268, -2), (key1651, -2), (key1268, -2), (key1648, -2), (key1648, -2), (key1265, -2)]

theorem rawRowCheck7956 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form0 = rawRow7956 := by decide +kernel

def row7956 : Integer.Sparse Key := [(key1256, 4), (key1261, 2), (key1265, -2), (key1268, -4), (key1609, 4), (key1642, 2), (key1648, -4), (key1651, -4), (key1674, -4), (key1806, 4), (key1809, 4), (key1832, 4), (key1837, -4), (key1848, -2)]

theorem rowCheck7956 : row7956 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7956 := by decide +kernel

theorem rowEval7956 (x : Key → ℝ) : Integer.Sparse.eval row7956 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7956, Integer.Sparse.eval_collectBalanced, rawRowCheck7956]

def rawRow7957 : Integer.Sparse Key := [(key1256, 2), (key1265, 2), (key1268, 2), (key1531, 2), (key1648, 2), (key1674, 2), (key1765, 2), (key1768, 2), (key1806, 2), (key1832, 2), (key1837, 2), (key1848, 2), (key1256, -2), (key1261, -2), (key1268, -2), (key1531, -2), (key1536, -2), (key1609, -2), (key1642, -2), (key1651, -2), (key1674, -2), (key1768, -2), (key1809, -2), (key1832, -2)]

theorem rawRowCheck7957 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form0 = rawRow7957 := by decide +kernel

def row7957 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7957 : row7957 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7957 := by decide +kernel

theorem rowEval7957 (x : Key → ℝ) : Integer.Sparse.eval row7957 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7957, Integer.Sparse.eval_collectBalanced, rawRowCheck7957]

def rawRow7958 : Integer.Sparse Key := [(key1256, 2), (key1268, 2), (key1265, 2), (key1531, 2), (key1674, 2), (key1648, 2), (key1768, 2), (key1765, 2), (key1832, 2), (key1806, 2), (key1848, 2), (key1837, 2), (key1261, -2), (key1256, -2), (key1268, -2), (key1536, -2), (key1531, -2), (key1642, -2), (key1609, -2), (key1674, -2), (key1651, -2), (key1768, -2), (key1832, -2), (key1809, -2)]

theorem rawRowCheck7958 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form0 = rawRow7958 := by decide +kernel

def row7958 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7958 : row7958 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7958 := by decide +kernel

theorem rowEval7958 (x : Key → ℝ) : Integer.Sparse.eval row7958 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7958, Integer.Sparse.eval_collectBalanced, rawRowCheck7958]

def rawRow7959 : Integer.Sparse Key := [(key1265, 2), (key1256, 2), (key1268, 2), (key1648, 2), (key1531, 2), (key1674, 2), (key1806, 2), (key1837, 2), (key1765, 2), (key1848, 2), (key1768, 2), (key1832, 2), (key1256, -2), (key1268, -2), (key1261, -2), (key1609, -2), (key1651, -2), (key1531, -2), (key1674, -2), (key1536, -2), (key1642, -2), (key1809, -2), (key1768, -2), (key1832, -2)]

theorem rawRowCheck7959 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form0 = rawRow7959 := by decide +kernel

def row7959 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7959 : row7959 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7959 := by decide +kernel

theorem rowEval7959 (x : Key → ℝ) : Integer.Sparse.eval row7959 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7959, Integer.Sparse.eval_collectBalanced, rawRowCheck7959]

def rawRow7960 : Integer.Sparse Key := [(key1265, 2), (key1268, 2), (key1256, 2), (key1648, 2), (key1674, 2), (key1531, 2), (key1837, 2), (key1806, 2), (key1848, 2), (key1765, 2), (key1832, 2), (key1768, 2), (key1268, -2), (key1256, -2), (key1261, -2), (key1651, -2), (key1609, -2), (key1674, -2), (key1531, -2), (key1642, -2), (key1536, -2), (key1809, -2), (key1832, -2), (key1768, -2)]

theorem rawRowCheck7960 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form0 = rawRow7960 := by decide +kernel

def row7960 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7960 : row7960 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7960 := by decide +kernel

theorem rowEval7960 (x : Key → ℝ) : Integer.Sparse.eval row7960 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7960, Integer.Sparse.eval_collectBalanced, rawRowCheck7960]

def rawRow7961 : Integer.Sparse Key := [(key1268, 2), (key1256, 2), (key1265, 2), (key1674, 2), (key1531, 2), (key1648, 2), (key1832, 2), (key1848, 2), (key1768, 2), (key1837, 2), (key1765, 2), (key1806, 2), (key1261, -2), (key1268, -2), (key1256, -2), (key1642, -2), (key1674, -2), (key1536, -2), (key1651, -2), (key1531, -2), (key1609, -2), (key1832, -2), (key1768, -2), (key1809, -2)]

theorem rawRowCheck7961 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form0 = rawRow7961 := by decide +kernel

def row7961 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7961 : row7961 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7961 := by decide +kernel

theorem rowEval7961 (x : Key → ℝ) : Integer.Sparse.eval row7961 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7961, Integer.Sparse.eval_collectBalanced, rawRowCheck7961]

def rawRow7962 : Integer.Sparse Key := [(key1268, 2), (key1265, 2), (key1256, 2), (key1674, 2), (key1648, 2), (key1531, 2), (key1848, 2), (key1832, 2), (key1837, 2), (key1768, 2), (key1806, 2), (key1765, 2), (key1268, -2), (key1261, -2), (key1256, -2), (key1674, -2), (key1642, -2), (key1651, -2), (key1536, -2), (key1609, -2), (key1531, -2), (key1832, -2), (key1809, -2), (key1768, -2)]

theorem rawRowCheck7962 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form0 = rawRow7962 := by decide +kernel

def row7962 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7962 : row7962 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7962 := by decide +kernel

theorem rowEval7962 (x : Key → ℝ) : Integer.Sparse.eval row7962 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7962, Integer.Sparse.eval_collectBalanced, rawRowCheck7962]

def rawRow7963 : Integer.Sparse Key := [(key1531, 2), (key1765, 2), (key1768, 2), (key1256, 2), (key1806, 2), (key1832, 2), (key1265, 2), (key1268, 2), (key1648, 2), (key1674, 2), (key1837, 2), (key1848, 2), (key1531, -2), (key1536, -2), (key1768, -2), (key1256, -2), (key1261, -2), (key1609, -2), (key1642, -2), (key1809, -2), (key1832, -2), (key1268, -2), (key1651, -2), (key1674, -2)]

theorem rawRowCheck7963 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form0 = rawRow7963 := by decide +kernel

def row7963 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7963 : row7963 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7963 := by decide +kernel

theorem rowEval7963 (x : Key → ℝ) : Integer.Sparse.eval row7963 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7963, Integer.Sparse.eval_collectBalanced, rawRowCheck7963]

def rawRow7964 : Integer.Sparse Key := [(key1531, 2), (key1768, 2), (key1765, 2), (key1256, 2), (key1832, 2), (key1806, 2), (key1268, 2), (key1265, 2), (key1674, 2), (key1648, 2), (key1848, 2), (key1837, 2), (key1536, -2), (key1531, -2), (key1768, -2), (key1261, -2), (key1256, -2), (key1642, -2), (key1609, -2), (key1832, -2), (key1809, -2), (key1268, -2), (key1674, -2), (key1651, -2)]

theorem rawRowCheck7964 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form0 = rawRow7964 := by decide +kernel

def row7964 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7964 : row7964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7964 := by decide +kernel

theorem rowEval7964 (x : Key → ℝ) : Integer.Sparse.eval row7964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7964, Integer.Sparse.eval_collectBalanced, rawRowCheck7964]

def rawRow7965 : Integer.Sparse Key := [(key1765, 2), (key1531, 2), (key1768, 2), (key1806, 2), (key1256, 2), (key1832, 2), (key1648, 2), (key1837, 2), (key1265, 2), (key1848, 2), (key1268, 2), (key1674, 2), (key1531, -2), (key1768, -2), (key1536, -2), (key1609, -2), (key1809, -2), (key1256, -2), (key1832, -2), (key1261, -2), (key1642, -2), (key1651, -2), (key1268, -2), (key1674, -2)]

theorem rawRowCheck7965 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form0 = rawRow7965 := by decide +kernel

def row7965 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7965 : row7965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7965 := by decide +kernel

theorem rowEval7965 (x : Key → ℝ) : Integer.Sparse.eval row7965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7965, Integer.Sparse.eval_collectBalanced, rawRowCheck7965]

def rawRow7966 : Integer.Sparse Key := [(key1765, 2), (key1768, 2), (key1531, 2), (key1806, 2), (key1832, 2), (key1256, 2), (key1837, 2), (key1648, 2), (key1848, 2), (key1265, 2), (key1674, 2), (key1268, 2), (key1768, -2), (key1531, -2), (key1536, -2), (key1809, -2), (key1609, -2), (key1832, -2), (key1256, -2), (key1642, -2), (key1261, -2), (key1651, -2), (key1674, -2), (key1268, -2)]

theorem rawRowCheck7966 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form0 = rawRow7966 := by decide +kernel

def row7966 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7966 : row7966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7966 := by decide +kernel

theorem rowEval7966 (x : Key → ℝ) : Integer.Sparse.eval row7966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7966, Integer.Sparse.eval_collectBalanced, rawRowCheck7966]

def rawRow7967 : Integer.Sparse Key := [(key1768, 2), (key1531, 2), (key1765, 2), (key1832, 2), (key1256, 2), (key1806, 2), (key1674, 2), (key1848, 2), (key1268, 2), (key1837, 2), (key1265, 2), (key1648, 2), (key1536, -2), (key1768, -2), (key1531, -2), (key1642, -2), (key1832, -2), (key1261, -2), (key1809, -2), (key1256, -2), (key1609, -2), (key1674, -2), (key1268, -2), (key1651, -2)]

theorem rawRowCheck7967 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form0 = rawRow7967 := by decide +kernel

def row7967 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7967 : row7967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7967 := by decide +kernel

theorem rowEval7967 (x : Key → ℝ) : Integer.Sparse.eval row7967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7967, Integer.Sparse.eval_collectBalanced, rawRowCheck7967]

def rawRow7968 : Integer.Sparse Key := [(key1768, 2), (key1765, 2), (key1531, 2), (key1832, 2), (key1806, 2), (key1256, 2), (key1848, 2), (key1674, 2), (key1837, 2), (key1268, 2), (key1648, 2), (key1265, 2), (key1768, -2), (key1536, -2), (key1531, -2), (key1832, -2), (key1642, -2), (key1809, -2), (key1261, -2), (key1609, -2), (key1256, -2), (key1674, -2), (key1651, -2), (key1268, -2)]

theorem rawRowCheck7968 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form0 = rawRow7968 := by decide +kernel

def row7968 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7968 : row7968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7968 := by decide +kernel

theorem rowEval7968 (x : Key → ℝ) : Integer.Sparse.eval row7968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7968, Integer.Sparse.eval_collectBalanced, rawRowCheck7968]

def rawRow7969 : Integer.Sparse Key := [(key1648, 2), (key1806, 2), (key1837, 2), (key1265, 2), (key1765, 2), (key1848, 2), (key1256, 2), (key1268, 2), (key1531, 2), (key1674, 2), (key1768, 2), (key1832, 2), (key1609, -2), (key1651, -2), (key1809, -2), (key1256, -2), (key1268, -2), (key1531, -2), (key1674, -2), (key1768, -2), (key1832, -2), (key1261, -2), (key1536, -2), (key1642, -2)]

theorem rawRowCheck7969 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form0 = rawRow7969 := by decide +kernel

def row7969 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7969 : row7969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7969 := by decide +kernel

theorem rowEval7969 (x : Key → ℝ) : Integer.Sparse.eval row7969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7969, Integer.Sparse.eval_collectBalanced, rawRowCheck7969]

def rawRow7970 : Integer.Sparse Key := [(key1648, 2), (key1837, 2), (key1806, 2), (key1265, 2), (key1848, 2), (key1765, 2), (key1268, 2), (key1256, 2), (key1674, 2), (key1531, 2), (key1832, 2), (key1768, 2), (key1651, -2), (key1609, -2), (key1809, -2), (key1268, -2), (key1256, -2), (key1674, -2), (key1531, -2), (key1832, -2), (key1768, -2), (key1261, -2), (key1642, -2), (key1536, -2)]

theorem rawRowCheck7970 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form0 = rawRow7970 := by decide +kernel

def row7970 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7970 : row7970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7970 := by decide +kernel

theorem rowEval7970 (x : Key → ℝ) : Integer.Sparse.eval row7970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7970, Integer.Sparse.eval_collectBalanced, rawRowCheck7970]

def rawRow7971 : Integer.Sparse Key := [(key1806, 2), (key1648, 2), (key1837, 2), (key1765, 2), (key1265, 2), (key1848, 2), (key1531, 2), (key1768, 2), (key1256, 2), (key1832, 2), (key1268, 2), (key1674, 2), (key1609, -2), (key1809, -2), (key1651, -2), (key1531, -2), (key1768, -2), (key1256, -2), (key1832, -2), (key1268, -2), (key1674, -2), (key1536, -2), (key1261, -2), (key1642, -2)]

theorem rawRowCheck7971 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form0 = rawRow7971 := by decide +kernel

def row7971 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7971 : row7971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7971 := by decide +kernel

theorem rowEval7971 (x : Key → ℝ) : Integer.Sparse.eval row7971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7971, Integer.Sparse.eval_collectBalanced, rawRowCheck7971]

def rawRow7972 : Integer.Sparse Key := [(key1806, 2), (key1837, 2), (key1648, 2), (key1765, 2), (key1848, 2), (key1265, 2), (key1768, 2), (key1531, 2), (key1832, 2), (key1256, 2), (key1674, 2), (key1268, 2), (key1809, -2), (key1609, -2), (key1651, -2), (key1768, -2), (key1531, -2), (key1832, -2), (key1256, -2), (key1674, -2), (key1268, -2), (key1536, -2), (key1642, -2), (key1261, -2)]

theorem rawRowCheck7972 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form0 = rawRow7972 := by decide +kernel

def row7972 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7972 : row7972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7972 := by decide +kernel

theorem rowEval7972 (x : Key → ℝ) : Integer.Sparse.eval row7972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7972, Integer.Sparse.eval_collectBalanced, rawRowCheck7972]

def rawRow7973 : Integer.Sparse Key := [(key1837, 2), (key1648, 2), (key1806, 2), (key1848, 2), (key1265, 2), (key1765, 2), (key1674, 2), (key1832, 2), (key1268, 2), (key1768, 2), (key1256, 2), (key1531, 2), (key1651, -2), (key1809, -2), (key1609, -2), (key1674, -2), (key1832, -2), (key1268, -2), (key1768, -2), (key1256, -2), (key1531, -2), (key1642, -2), (key1261, -2), (key1536, -2)]

theorem rawRowCheck7973 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form0 = rawRow7973 := by decide +kernel

def row7973 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7973 : row7973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7973 := by decide +kernel

theorem rowEval7973 (x : Key → ℝ) : Integer.Sparse.eval row7973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7973, Integer.Sparse.eval_collectBalanced, rawRowCheck7973]

def rawRow7974 : Integer.Sparse Key := [(key1837, 2), (key1806, 2), (key1648, 2), (key1848, 2), (key1765, 2), (key1265, 2), (key1832, 2), (key1674, 2), (key1768, 2), (key1268, 2), (key1531, 2), (key1256, 2), (key1809, -2), (key1651, -2), (key1609, -2), (key1832, -2), (key1674, -2), (key1768, -2), (key1268, -2), (key1531, -2), (key1256, -2), (key1642, -2), (key1536, -2), (key1261, -2)]

theorem rawRowCheck7974 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form0 = rawRow7974 := by decide +kernel

def row7974 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7974 : row7974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7974 := by decide +kernel

theorem rowEval7974 (x : Key → ℝ) : Integer.Sparse.eval row7974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7974, Integer.Sparse.eval_collectBalanced, rawRowCheck7974]

def rawRow7975 : Integer.Sparse Key := [(key1674, 2), (key1832, 2), (key1848, 2), (key1268, 2), (key1768, 2), (key1837, 2), (key1256, 2), (key1265, 2), (key1531, 2), (key1648, 2), (key1765, 2), (key1806, 2), (key1642, -2), (key1674, -2), (key1832, -2), (key1261, -2), (key1268, -2), (key1536, -2), (key1651, -2), (key1768, -2), (key1809, -2), (key1256, -2), (key1531, -2), (key1609, -2)]

theorem rawRowCheck7975 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form0 = rawRow7975 := by decide +kernel

def row7975 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7975 : row7975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7975 := by decide +kernel

theorem rowEval7975 (x : Key → ℝ) : Integer.Sparse.eval row7975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7975, Integer.Sparse.eval_collectBalanced, rawRowCheck7975]

def rawRow7976 : Integer.Sparse Key := [(key1674, 2), (key1848, 2), (key1832, 2), (key1268, 2), (key1837, 2), (key1768, 2), (key1265, 2), (key1256, 2), (key1648, 2), (key1531, 2), (key1806, 2), (key1765, 2), (key1674, -2), (key1642, -2), (key1832, -2), (key1268, -2), (key1261, -2), (key1651, -2), (key1536, -2), (key1809, -2), (key1768, -2), (key1256, -2), (key1609, -2), (key1531, -2)]

theorem rawRowCheck7976 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form0 = rawRow7976 := by decide +kernel

def row7976 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7976 : row7976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7976 := by decide +kernel

theorem rowEval7976 (x : Key → ℝ) : Integer.Sparse.eval row7976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7976, Integer.Sparse.eval_collectBalanced, rawRowCheck7976]

def rawRow7977 : Integer.Sparse Key := [(key1832, 2), (key1674, 2), (key1848, 2), (key1768, 2), (key1268, 2), (key1837, 2), (key1531, 2), (key1765, 2), (key1256, 2), (key1806, 2), (key1265, 2), (key1648, 2), (key1642, -2), (key1832, -2), (key1674, -2), (key1536, -2), (key1768, -2), (key1261, -2), (key1809, -2), (key1268, -2), (key1651, -2), (key1531, -2), (key1256, -2), (key1609, -2)]

theorem rawRowCheck7977 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form0 = rawRow7977 := by decide +kernel

def row7977 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7977 : row7977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7977 := by decide +kernel

theorem rowEval7977 (x : Key → ℝ) : Integer.Sparse.eval row7977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck7977, Integer.Sparse.eval_collectBalanced, rawRowCheck7977]

def rawRow7978 : Integer.Sparse Key := [(key1832, 2), (key1848, 2), (key1674, 2), (key1768, 2), (key1837, 2), (key1268, 2), (key1765, 2), (key1531, 2), (key1806, 2), (key1256, 2), (key1648, 2), (key1265, 2), (key1832, -2), (key1642, -2), (key1674, -2), (key1768, -2), (key1536, -2), (key1809, -2), (key1261, -2), (key1651, -2), (key1268, -2), (key1531, -2), (key1609, -2), (key1256, -2)]

theorem rawRowCheck7978 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form0 = rawRow7978 := by decide +kernel

def row7978 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7978 : row7978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7978 := by decide +kernel

theorem rowEval7978 (x : Key → ℝ) : Integer.Sparse.eval row7978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7978, Integer.Sparse.eval_collectBalanced, rawRowCheck7978]

def rawRow7979 : Integer.Sparse Key := [(key1848, 2), (key1674, 2), (key1832, 2), (key1837, 2), (key1268, 2), (key1768, 2), (key1648, 2), (key1806, 2), (key1265, 2), (key1765, 2), (key1256, 2), (key1531, 2), (key1674, -2), (key1832, -2), (key1642, -2), (key1651, -2), (key1809, -2), (key1268, -2), (key1768, -2), (key1261, -2), (key1536, -2), (key1609, -2), (key1256, -2), (key1531, -2)]

theorem rawRowCheck7979 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form0 = rawRow7979 := by decide +kernel

def row7979 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7979 : row7979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7979 := by decide +kernel

theorem rowEval7979 (x : Key → ℝ) : Integer.Sparse.eval row7979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form0) x := by
  rw [rowCheck7979, Integer.Sparse.eval_collectBalanced, rawRowCheck7979]

def rawRow7980 : Integer.Sparse Key := [(key1848, 2), (key1832, 2), (key1674, 2), (key1837, 2), (key1768, 2), (key1268, 2), (key1806, 2), (key1648, 2), (key1765, 2), (key1265, 2), (key1531, 2), (key1256, 2), (key1832, -2), (key1674, -2), (key1642, -2), (key1809, -2), (key1651, -2), (key1768, -2), (key1268, -2), (key1536, -2), (key1261, -2), (key1609, -2), (key1531, -2), (key1256, -2)]

theorem rawRowCheck7980 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form0 = rawRow7980 := by decide +kernel

def row7980 : Integer.Sparse Key := [(key1261, -2), (key1265, 2), (key1536, -2), (key1609, -2), (key1642, -2), (key1648, 2), (key1651, -2), (key1765, 2), (key1806, 2), (key1809, -2), (key1837, 2), (key1848, 2)]

theorem rowCheck7980 : row7980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7980 := by decide +kernel

theorem rowEval7980 (x : Key → ℝ) : Integer.Sparse.eval row7980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck7980, Integer.Sparse.eval_collectBalanced, rawRowCheck7980]

def rawRow7981 : Integer.Sparse Key := [(key377, -24), (key208, 6), (key428, 6), (key428, 6), (key456, 6)]

theorem rawRowCheck7981 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form1 = rawRow7981 := by decide +kernel

def row7981 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

theorem rowCheck7981 : row7981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7981 := by decide +kernel

theorem rowEval7981 (x : Key → ℝ) : Integer.Sparse.eval row7981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7981, Integer.Sparse.eval_collectBalanced, rawRowCheck7981]

def rawRow7982 : Integer.Sparse Key := [(key377, -24), (key208, 6), (key428, 6), (key456, 6), (key428, 6)]

theorem rawRowCheck7982 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form1 = rawRow7982 := by decide +kernel

def row7982 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

theorem rowCheck7982 : row7982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7982 := by decide +kernel

theorem rowEval7982 (x : Key → ℝ) : Integer.Sparse.eval row7982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7982, Integer.Sparse.eval_collectBalanced, rawRowCheck7982]

def rawRow7983 : Integer.Sparse Key := [(key377, -24), (key208, 6), (key456, 6), (key428, 6), (key428, 6)]

theorem rawRowCheck7983 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form1 = rawRow7983 := by decide +kernel

def row7983 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

theorem rowCheck7983 : row7983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7983 := by decide +kernel

theorem rowEval7983 (x : Key → ℝ) : Integer.Sparse.eval row7983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7983, Integer.Sparse.eval_collectBalanced, rawRowCheck7983]

def rawRow7984 : Integer.Sparse Key := [(key377, -24), (key428, 6), (key208, 6), (key428, 6), (key456, 6)]

theorem rawRowCheck7984 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form1 = rawRow7984 := by decide +kernel

def row7984 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

theorem rowCheck7984 : row7984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7984 := by decide +kernel

theorem rowEval7984 (x : Key → ℝ) : Integer.Sparse.eval row7984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7984, Integer.Sparse.eval_collectBalanced, rawRowCheck7984]

def rawRow7985 : Integer.Sparse Key := [(key377, -24), (key428, 6), (key208, 6), (key456, 6), (key428, 6)]

theorem rawRowCheck7985 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form1 = rawRow7985 := by decide +kernel

def row7985 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

theorem rowCheck7985 : row7985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7985 := by decide +kernel

theorem rowEval7985 (x : Key → ℝ) : Integer.Sparse.eval row7985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7985, Integer.Sparse.eval_collectBalanced, rawRowCheck7985]

def rawRow7986 : Integer.Sparse Key := [(key377, -24), (key428, 6), (key428, 6), (key208, 6), (key456, 6)]

theorem rawRowCheck7986 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form1 = rawRow7986 := by decide +kernel

def row7986 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

theorem rowCheck7986 : row7986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7986 := by decide +kernel

theorem rowEval7986 (x : Key → ℝ) : Integer.Sparse.eval row7986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7986, Integer.Sparse.eval_collectBalanced, rawRowCheck7986]

def rawRow7987 : Integer.Sparse Key := [(key377, -24), (key428, 6), (key428, 6), (key456, 6), (key208, 6)]

theorem rawRowCheck7987 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form1 = rawRow7987 := by decide +kernel

def row7987 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

theorem rowCheck7987 : row7987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7987 := by decide +kernel

theorem rowEval7987 (x : Key → ℝ) : Integer.Sparse.eval row7987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7987, Integer.Sparse.eval_collectBalanced, rawRowCheck7987]

def rawRow7988 : Integer.Sparse Key := [(key377, -24), (key428, 6), (key456, 6), (key208, 6), (key428, 6)]

theorem rawRowCheck7988 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form1 = rawRow7988 := by decide +kernel

def row7988 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

theorem rowCheck7988 : row7988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7988 := by decide +kernel

theorem rowEval7988 (x : Key → ℝ) : Integer.Sparse.eval row7988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7988, Integer.Sparse.eval_collectBalanced, rawRowCheck7988]

def rawRow7989 : Integer.Sparse Key := [(key377, -24), (key428, 6), (key456, 6), (key428, 6), (key208, 6)]

theorem rawRowCheck7989 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form1 = rawRow7989 := by decide +kernel

def row7989 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

theorem rowCheck7989 : row7989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7989 := by decide +kernel

theorem rowEval7989 (x : Key → ℝ) : Integer.Sparse.eval row7989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7989, Integer.Sparse.eval_collectBalanced, rawRowCheck7989]

def rawRow7990 : Integer.Sparse Key := [(key377, -24), (key456, 6), (key208, 6), (key428, 6), (key428, 6)]

theorem rawRowCheck7990 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form1 = rawRow7990 := by decide +kernel

def row7990 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

theorem rowCheck7990 : row7990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7990 := by decide +kernel

theorem rowEval7990 (x : Key → ℝ) : Integer.Sparse.eval row7990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7990, Integer.Sparse.eval_collectBalanced, rawRowCheck7990]

def rawRow7991 : Integer.Sparse Key := [(key377, -24), (key456, 6), (key428, 6), (key208, 6), (key428, 6)]

theorem rawRowCheck7991 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form1 = rawRow7991 := by decide +kernel

def row7991 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

theorem rowCheck7991 : row7991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7991 := by decide +kernel

theorem rowEval7991 (x : Key → ℝ) : Integer.Sparse.eval row7991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7991, Integer.Sparse.eval_collectBalanced, rawRowCheck7991]

def rawRow7992 : Integer.Sparse Key := [(key377, -24), (key456, 6), (key428, 6), (key428, 6), (key208, 6)]

theorem rawRowCheck7992 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form1 = rawRow7992 := by decide +kernel

def row7992 : Integer.Sparse Key := [(key208, 6), (key377, -24), (key428, 12), (key456, 6)]

theorem rowCheck7992 : row7992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7992 := by decide +kernel

theorem rowEval7992 (x : Key → ℝ) : Integer.Sparse.eval row7992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7992, Integer.Sparse.eval_collectBalanced, rawRowCheck7992]

def rawRow7993 : Integer.Sparse Key := [(key428, -24), (key208, 6), (key377, 6), (key428, 6), (key456, 6)]

theorem rawRowCheck7993 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form1 = rawRow7993 := by decide +kernel

def row7993 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck7993 : row7993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7993 := by decide +kernel

theorem rowEval7993 (x : Key → ℝ) : Integer.Sparse.eval row7993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7993, Integer.Sparse.eval_collectBalanced, rawRowCheck7993]

def rawRow7994 : Integer.Sparse Key := [(key428, -24), (key208, 6), (key377, 6), (key456, 6), (key428, 6)]

theorem rawRowCheck7994 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form1 = rawRow7994 := by decide +kernel

def row7994 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck7994 : row7994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7994 := by decide +kernel

theorem rowEval7994 (x : Key → ℝ) : Integer.Sparse.eval row7994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7994, Integer.Sparse.eval_collectBalanced, rawRowCheck7994]

def rawRow7995 : Integer.Sparse Key := [(key428, -24), (key208, 6), (key428, 6), (key377, 6), (key456, 6)]

theorem rawRowCheck7995 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form1 = rawRow7995 := by decide +kernel

def row7995 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck7995 : row7995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7995 := by decide +kernel

theorem rowEval7995 (x : Key → ℝ) : Integer.Sparse.eval row7995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7995, Integer.Sparse.eval_collectBalanced, rawRowCheck7995]

def rawRow7996 : Integer.Sparse Key := [(key428, -24), (key208, 6), (key428, 6), (key456, 6), (key377, 6)]

theorem rawRowCheck7996 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form1 = rawRow7996 := by decide +kernel

def row7996 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck7996 : row7996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7996 := by decide +kernel

theorem rowEval7996 (x : Key → ℝ) : Integer.Sparse.eval row7996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7996, Integer.Sparse.eval_collectBalanced, rawRowCheck7996]

def rawRow7997 : Integer.Sparse Key := [(key428, -24), (key208, 6), (key456, 6), (key377, 6), (key428, 6)]

theorem rawRowCheck7997 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form1 = rawRow7997 := by decide +kernel

def row7997 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck7997 : row7997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7997 := by decide +kernel

theorem rowEval7997 (x : Key → ℝ) : Integer.Sparse.eval row7997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck7997, Integer.Sparse.eval_collectBalanced, rawRowCheck7997]

def rawRow7998 : Integer.Sparse Key := [(key428, -24), (key208, 6), (key456, 6), (key428, 6), (key377, 6)]

theorem rawRowCheck7998 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form1 = rawRow7998 := by decide +kernel

def row7998 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck7998 : row7998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7998 := by decide +kernel

theorem rowEval7998 (x : Key → ℝ) : Integer.Sparse.eval row7998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck7998, Integer.Sparse.eval_collectBalanced, rawRowCheck7998]

def rawRow7999 : Integer.Sparse Key := [(key428, -24), (key377, 6), (key208, 6), (key428, 6), (key456, 6)]

theorem rawRowCheck7999 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form1 = rawRow7999 := by decide +kernel

def row7999 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck7999 : row7999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7999 := by decide +kernel

theorem rowEval7999 (x : Key → ℝ) : Integer.Sparse.eval row7999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck7999, Integer.Sparse.eval_collectBalanced, rawRowCheck7999]

def rawRow8000 : Integer.Sparse Key := [(key428, -24), (key377, 6), (key208, 6), (key456, 6), (key428, 6)]

theorem rawRowCheck8000 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form1 = rawRow8000 := by decide +kernel

def row8000 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck8000 : row8000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8000 := by decide +kernel

theorem rowEval8000 (x : Key → ℝ) : Integer.Sparse.eval row8000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8000, Integer.Sparse.eval_collectBalanced, rawRowCheck8000]

def rawRow8001 : Integer.Sparse Key := [(key428, -24), (key377, 6), (key428, 6), (key208, 6), (key456, 6)]

theorem rawRowCheck8001 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form1 = rawRow8001 := by decide +kernel

def row8001 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck8001 : row8001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8001 := by decide +kernel

theorem rowEval8001 (x : Key → ℝ) : Integer.Sparse.eval row8001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8001, Integer.Sparse.eval_collectBalanced, rawRowCheck8001]

def rawRow8002 : Integer.Sparse Key := [(key428, -24), (key377, 6), (key428, 6), (key456, 6), (key208, 6)]

theorem rawRowCheck8002 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form1 = rawRow8002 := by decide +kernel

def row8002 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck8002 : row8002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8002 := by decide +kernel

theorem rowEval8002 (x : Key → ℝ) : Integer.Sparse.eval row8002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8002, Integer.Sparse.eval_collectBalanced, rawRowCheck8002]

def rawRow8003 : Integer.Sparse Key := [(key428, -24), (key377, 6), (key456, 6), (key208, 6), (key428, 6)]

theorem rawRowCheck8003 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form1 = rawRow8003 := by decide +kernel

def row8003 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck8003 : row8003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8003 := by decide +kernel

theorem rowEval8003 (x : Key → ℝ) : Integer.Sparse.eval row8003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8003, Integer.Sparse.eval_collectBalanced, rawRowCheck8003]

def rawRow8004 : Integer.Sparse Key := [(key428, -24), (key377, 6), (key456, 6), (key428, 6), (key208, 6)]

theorem rawRowCheck8004 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form1 = rawRow8004 := by decide +kernel

def row8004 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck8004 : row8004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8004 := by decide +kernel

theorem rowEval8004 (x : Key → ℝ) : Integer.Sparse.eval row8004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8004, Integer.Sparse.eval_collectBalanced, rawRowCheck8004]

def rawRow8005 : Integer.Sparse Key := [(key428, -24), (key428, 6), (key208, 6), (key377, 6), (key456, 6)]

theorem rawRowCheck8005 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form1 = rawRow8005 := by decide +kernel

def row8005 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck8005 : row8005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8005 := by decide +kernel

theorem rowEval8005 (x : Key → ℝ) : Integer.Sparse.eval row8005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8005, Integer.Sparse.eval_collectBalanced, rawRowCheck8005]

def rawRow8006 : Integer.Sparse Key := [(key428, -24), (key428, 6), (key208, 6), (key456, 6), (key377, 6)]

theorem rawRowCheck8006 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form1 = rawRow8006 := by decide +kernel

def row8006 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck8006 : row8006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8006 := by decide +kernel

theorem rowEval8006 (x : Key → ℝ) : Integer.Sparse.eval row8006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8006, Integer.Sparse.eval_collectBalanced, rawRowCheck8006]

def rawRow8007 : Integer.Sparse Key := [(key428, -24), (key428, 6), (key377, 6), (key208, 6), (key456, 6)]

theorem rawRowCheck8007 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form1 = rawRow8007 := by decide +kernel

def row8007 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck8007 : row8007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8007 := by decide +kernel

theorem rowEval8007 (x : Key → ℝ) : Integer.Sparse.eval row8007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8007, Integer.Sparse.eval_collectBalanced, rawRowCheck8007]

def rawRow8008 : Integer.Sparse Key := [(key428, -24), (key428, 6), (key377, 6), (key456, 6), (key208, 6)]

theorem rawRowCheck8008 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form1 = rawRow8008 := by decide +kernel

def row8008 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck8008 : row8008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8008 := by decide +kernel

theorem rowEval8008 (x : Key → ℝ) : Integer.Sparse.eval row8008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8008, Integer.Sparse.eval_collectBalanced, rawRowCheck8008]

def rawRow8009 : Integer.Sparse Key := [(key428, -24), (key428, 6), (key456, 6), (key208, 6), (key377, 6)]

theorem rawRowCheck8009 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form1 = rawRow8009 := by decide +kernel

def row8009 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck8009 : row8009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8009 := by decide +kernel

theorem rowEval8009 (x : Key → ℝ) : Integer.Sparse.eval row8009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8009, Integer.Sparse.eval_collectBalanced, rawRowCheck8009]

def rawRow8010 : Integer.Sparse Key := [(key428, -24), (key428, 6), (key456, 6), (key377, 6), (key208, 6)]

theorem rawRowCheck8010 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form1 = rawRow8010 := by decide +kernel

def row8010 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck8010 : row8010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8010 := by decide +kernel

theorem rowEval8010 (x : Key → ℝ) : Integer.Sparse.eval row8010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8010, Integer.Sparse.eval_collectBalanced, rawRowCheck8010]

def rawRow8011 : Integer.Sparse Key := [(key428, -24), (key456, 6), (key208, 6), (key377, 6), (key428, 6)]

theorem rawRowCheck8011 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form1 = rawRow8011 := by decide +kernel

def row8011 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck8011 : row8011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8011 := by decide +kernel

theorem rowEval8011 (x : Key → ℝ) : Integer.Sparse.eval row8011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8011, Integer.Sparse.eval_collectBalanced, rawRowCheck8011]

def rawRow8012 : Integer.Sparse Key := [(key428, -24), (key456, 6), (key208, 6), (key428, 6), (key377, 6)]

theorem rawRowCheck8012 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form1 = rawRow8012 := by decide +kernel

def row8012 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck8012 : row8012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8012 := by decide +kernel

theorem rowEval8012 (x : Key → ℝ) : Integer.Sparse.eval row8012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8012, Integer.Sparse.eval_collectBalanced, rawRowCheck8012]

def rawRow8013 : Integer.Sparse Key := [(key428, -24), (key456, 6), (key377, 6), (key208, 6), (key428, 6)]

theorem rawRowCheck8013 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form1 = rawRow8013 := by decide +kernel

def row8013 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck8013 : row8013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8013 := by decide +kernel

theorem rowEval8013 (x : Key → ℝ) : Integer.Sparse.eval row8013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck8013, Integer.Sparse.eval_collectBalanced, rawRowCheck8013]

def rawRow8014 : Integer.Sparse Key := [(key428, -24), (key456, 6), (key377, 6), (key428, 6), (key208, 6)]

theorem rawRowCheck8014 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form1 = rawRow8014 := by decide +kernel

def row8014 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck8014 : row8014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8014 := by decide +kernel

theorem rowEval8014 (x : Key → ℝ) : Integer.Sparse.eval row8014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8014, Integer.Sparse.eval_collectBalanced, rawRowCheck8014]

def rawRow8015 : Integer.Sparse Key := [(key428, -24), (key456, 6), (key428, 6), (key208, 6), (key377, 6)]

theorem rawRowCheck8015 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form1 = rawRow8015 := by decide +kernel

def row8015 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck8015 : row8015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8015 := by decide +kernel

theorem rowEval8015 (x : Key → ℝ) : Integer.Sparse.eval row8015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form1) x := by
  rw [rowCheck8015, Integer.Sparse.eval_collectBalanced, rawRowCheck8015]

def rawRow8016 : Integer.Sparse Key := [(key428, -24), (key456, 6), (key428, 6), (key377, 6), (key208, 6)]

theorem rawRowCheck8016 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form1 = rawRow8016 := by decide +kernel

def row8016 : Integer.Sparse Key := [(key208, 6), (key377, 6), (key428, -18), (key456, 6)]

theorem rowCheck8016 : row8016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8016 := by decide +kernel

theorem rowEval8016 (x : Key → ℝ) : Integer.Sparse.eval row8016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck8016, Integer.Sparse.eval_collectBalanced, rawRowCheck8016]

def rawRow8017 : Integer.Sparse Key := [(key43, -6), (key48, -6), (key48, -6), (key74, -6), (key206, 2), (key212, 2), (key212, 2), (key426, 2), (key432, 2), (key426, 2), (key460, 2), (key432, 2), (key460, 2), (key659, 2), (key659, 2), (key663, 2)]

theorem rawRowCheck8017 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form2 = rawRow8017 := by decide +kernel

def row8017 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

theorem rowCheck8017 : row8017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8017 := by decide +kernel

theorem rowEval8017 (x : Key → ℝ) : Integer.Sparse.eval row8017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8017, Integer.Sparse.eval_collectBalanced, rawRowCheck8017]

def rawRow8018 : Integer.Sparse Key := [(key48, -6), (key43, -6), (key48, -6), (key74, -6), (key212, 2), (key206, 2), (key212, 2), (key432, 2), (key426, 2), (key460, 2), (key426, 2), (key460, 2), (key432, 2), (key659, 2), (key663, 2), (key659, 2)]

theorem rawRowCheck8018 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form2 = rawRow8018 := by decide +kernel

def row8018 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

theorem rowCheck8018 : row8018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8018 := by decide +kernel

theorem rowEval8018 (x : Key → ℝ) : Integer.Sparse.eval row8018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8018, Integer.Sparse.eval_collectBalanced, rawRowCheck8018]

def rawRow8019 : Integer.Sparse Key := [(key48, -6), (key48, -6), (key43, -6), (key74, -6), (key212, 2), (key212, 2), (key206, 2), (key460, 2), (key460, 2), (key432, 2), (key432, 2), (key426, 2), (key426, 2), (key663, 2), (key659, 2), (key659, 2)]

theorem rawRowCheck8019 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form2 = rawRow8019 := by decide +kernel

def row8019 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

theorem rowCheck8019 : row8019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8019 := by decide +kernel

theorem rowEval8019 (x : Key → ℝ) : Integer.Sparse.eval row8019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8019, Integer.Sparse.eval_collectBalanced, rawRowCheck8019]

def rawRow8020 : Integer.Sparse Key := [(key43, -6), (key48, -6), (key74, -6), (key48, -6), (key426, 2), (key432, 2), (key659, 2), (key206, 2), (key212, 2), (key426, 2), (key460, 2), (key659, 2), (key663, 2), (key212, 2), (key432, 2), (key460, 2)]

theorem rawRowCheck8020 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form2 = rawRow8020 := by decide +kernel

def row8020 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

theorem rowCheck8020 : row8020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8020 := by decide +kernel

theorem rowEval8020 (x : Key → ℝ) : Integer.Sparse.eval row8020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8020, Integer.Sparse.eval_collectBalanced, rawRowCheck8020]

def rawRow8021 : Integer.Sparse Key := [(key48, -6), (key43, -6), (key74, -6), (key48, -6), (key432, 2), (key426, 2), (key659, 2), (key212, 2), (key206, 2), (key460, 2), (key426, 2), (key663, 2), (key659, 2), (key212, 2), (key460, 2), (key432, 2)]

theorem rawRowCheck8021 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form2 = rawRow8021 := by decide +kernel

def row8021 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

theorem rowCheck8021 : row8021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8021 := by decide +kernel

theorem rowEval8021 (x : Key → ℝ) : Integer.Sparse.eval row8021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8021, Integer.Sparse.eval_collectBalanced, rawRowCheck8021]

def rawRow8022 : Integer.Sparse Key := [(key43, -6), (key74, -6), (key48, -6), (key48, -6), (key426, 2), (key659, 2), (key432, 2), (key426, 2), (key659, 2), (key206, 2), (key663, 2), (key212, 2), (key460, 2), (key432, 2), (key212, 2), (key460, 2)]

theorem rawRowCheck8022 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form2 = rawRow8022 := by decide +kernel

def row8022 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

theorem rowCheck8022 : row8022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8022 := by decide +kernel

theorem rowEval8022 (x : Key → ℝ) : Integer.Sparse.eval row8022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8022, Integer.Sparse.eval_collectBalanced, rawRowCheck8022]

def rawRow8023 : Integer.Sparse Key := [(key74, -6), (key43, -6), (key48, -6), (key48, -6), (key659, 2), (key426, 2), (key432, 2), (key659, 2), (key426, 2), (key663, 2), (key206, 2), (key460, 2), (key212, 2), (key432, 2), (key460, 2), (key212, 2)]

theorem rawRowCheck8023 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form2 = rawRow8023 := by decide +kernel

def row8023 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

theorem rowCheck8023 : row8023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8023 := by decide +kernel

theorem rowEval8023 (x : Key → ℝ) : Integer.Sparse.eval row8023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8023, Integer.Sparse.eval_collectBalanced, rawRowCheck8023]

def rawRow8024 : Integer.Sparse Key := [(key48, -6), (key74, -6), (key43, -6), (key48, -6), (key432, 2), (key659, 2), (key426, 2), (key460, 2), (key663, 2), (key212, 2), (key659, 2), (key206, 2), (key426, 2), (key460, 2), (key212, 2), (key432, 2)]

theorem rawRowCheck8024 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form2 = rawRow8024 := by decide +kernel

def row8024 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

theorem rowCheck8024 : row8024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8024 := by decide +kernel

theorem rowEval8024 (x : Key → ℝ) : Integer.Sparse.eval row8024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8024, Integer.Sparse.eval_collectBalanced, rawRowCheck8024]

def rawRow8025 : Integer.Sparse Key := [(key74, -6), (key48, -6), (key43, -6), (key48, -6), (key659, 2), (key432, 2), (key426, 2), (key663, 2), (key460, 2), (key659, 2), (key212, 2), (key426, 2), (key206, 2), (key460, 2), (key432, 2), (key212, 2)]

theorem rawRowCheck8025 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form2 = rawRow8025 := by decide +kernel

def row8025 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

theorem rowCheck8025 : row8025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8025 := by decide +kernel

theorem rowEval8025 (x : Key → ℝ) : Integer.Sparse.eval row8025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8025, Integer.Sparse.eval_collectBalanced, rawRowCheck8025]

def rawRow8026 : Integer.Sparse Key := [(key48, -6), (key48, -6), (key74, -6), (key43, -6), (key460, 2), (key460, 2), (key663, 2), (key212, 2), (key212, 2), (key432, 2), (key432, 2), (key659, 2), (key659, 2), (key206, 2), (key426, 2), (key426, 2)]

theorem rawRowCheck8026 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form2 = rawRow8026 := by decide +kernel

def row8026 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

theorem rowCheck8026 : row8026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8026 := by decide +kernel

theorem rowEval8026 (x : Key → ℝ) : Integer.Sparse.eval row8026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8026, Integer.Sparse.eval_collectBalanced, rawRowCheck8026]

def rawRow8027 : Integer.Sparse Key := [(key48, -6), (key74, -6), (key48, -6), (key43, -6), (key460, 2), (key663, 2), (key460, 2), (key432, 2), (key659, 2), (key212, 2), (key659, 2), (key212, 2), (key432, 2), (key426, 2), (key206, 2), (key426, 2)]

theorem rawRowCheck8027 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form2 = rawRow8027 := by decide +kernel

def row8027 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

theorem rowCheck8027 : row8027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8027 := by decide +kernel

theorem rowEval8027 (x : Key → ℝ) : Integer.Sparse.eval row8027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8027, Integer.Sparse.eval_collectBalanced, rawRowCheck8027]

def rawRow8028 : Integer.Sparse Key := [(key74, -6), (key48, -6), (key48, -6), (key43, -6), (key663, 2), (key460, 2), (key460, 2), (key659, 2), (key432, 2), (key659, 2), (key212, 2), (key432, 2), (key212, 2), (key426, 2), (key426, 2), (key206, 2)]

theorem rawRowCheck8028 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form2 = rawRow8028 := by decide +kernel

def row8028 : Integer.Sparse Key := [(key43, -6), (key48, -12), (key74, -6), (key206, 2), (key212, 4), (key426, 4), (key432, 4), (key460, 4), (key659, 4), (key663, 2)]

theorem rowCheck8028 : row8028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8028 := by decide +kernel

theorem rowEval8028 (x : Key → ℝ) : Integer.Sparse.eval row8028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8028, Integer.Sparse.eval_collectBalanced, rawRowCheck8028]

def rawRow8029 : Integer.Sparse Key := [(key100, -6), (key105, -6), (key115, -6), (key137, -6), (key18, 2), (key23, 2), (key35, 2), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

theorem rawRowCheck8029 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form2 = rawRow8029 := by decide +kernel

def row8029 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

theorem rowCheck8029 : row8029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8029 := by decide +kernel

theorem rowEval8029 (x : Key → ℝ) : Integer.Sparse.eval row8029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8029, Integer.Sparse.eval_collectBalanced, rawRowCheck8029]

def rawRow8030 : Integer.Sparse Key := [(key105, -6), (key100, -6), (key115, -6), (key137, -6), (key23, 2), (key18, 2), (key35, 2), (key381, 2), (key375, 2), (key460, 2), (key426, 2), (key490, 2), (key486, 2), (key654, 2), (key663, 2), (key659, 2)]

theorem rawRowCheck8030 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form2 = rawRow8030 := by decide +kernel

def row8030 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

theorem rowCheck8030 : row8030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8030 := by decide +kernel

theorem rowEval8030 (x : Key → ℝ) : Integer.Sparse.eval row8030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8030, Integer.Sparse.eval_collectBalanced, rawRowCheck8030]

def rawRow8031 : Integer.Sparse Key := [(key100, -6), (key115, -6), (key105, -6), (key137, -6), (key18, 2), (key35, 2), (key23, 2), (key426, 2), (key486, 2), (key375, 2), (key490, 2), (key381, 2), (key460, 2), (key659, 2), (key654, 2), (key663, 2)]

theorem rawRowCheck8031 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form2 = rawRow8031 := by decide +kernel

def row8031 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

theorem rowCheck8031 : row8031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8031 := by decide +kernel

theorem rowEval8031 (x : Key → ℝ) : Integer.Sparse.eval row8031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8031, Integer.Sparse.eval_collectBalanced, rawRowCheck8031]

def rawRow8032 : Integer.Sparse Key := [(key115, -6), (key100, -6), (key105, -6), (key137, -6), (key35, 2), (key18, 2), (key23, 2), (key486, 2), (key426, 2), (key490, 2), (key375, 2), (key460, 2), (key381, 2), (key659, 2), (key663, 2), (key654, 2)]

theorem rawRowCheck8032 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form2 = rawRow8032 := by decide +kernel

def row8032 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

theorem rowCheck8032 : row8032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8032 := by decide +kernel

theorem rowEval8032 (x : Key → ℝ) : Integer.Sparse.eval row8032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8032, Integer.Sparse.eval_collectBalanced, rawRowCheck8032]

def rawRow8033 : Integer.Sparse Key := [(key105, -6), (key115, -6), (key100, -6), (key137, -6), (key23, 2), (key35, 2), (key18, 2), (key460, 2), (key490, 2), (key381, 2), (key486, 2), (key375, 2), (key426, 2), (key663, 2), (key654, 2), (key659, 2)]

theorem rawRowCheck8033 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form2 = rawRow8033 := by decide +kernel

def row8033 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

theorem rowCheck8033 : row8033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8033 := by decide +kernel

theorem rowEval8033 (x : Key → ℝ) : Integer.Sparse.eval row8033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8033, Integer.Sparse.eval_collectBalanced, rawRowCheck8033]

def rawRow8034 : Integer.Sparse Key := [(key115, -6), (key105, -6), (key100, -6), (key137, -6), (key35, 2), (key23, 2), (key18, 2), (key490, 2), (key460, 2), (key486, 2), (key381, 2), (key426, 2), (key375, 2), (key663, 2), (key659, 2), (key654, 2)]

theorem rawRowCheck8034 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form2 = rawRow8034 := by decide +kernel

def row8034 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key375, 2), (key381, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key654, 2), (key659, 2), (key663, 2)]

theorem rowCheck8034 : row8034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8034 := by decide +kernel

theorem rowEval8034 (x : Key → ℝ) : Integer.Sparse.eval row8034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8034, Integer.Sparse.eval_collectBalanced, rawRowCheck8034]

def rawRow8035 : Integer.Sparse Key := [(key100, -6), (key105, -6), (key137, -6), (key115, -6), (key43, 2), (key48, 2), (key74, 2), (key206, 2), (key212, 2), (key426, 2), (key460, 2), (key659, 2), (key663, 2), (key218, 2), (key486, 2), (key490, 2)]

theorem rawRowCheck8035 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form2 = rawRow8035 := by decide +kernel

def row8035 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key206, 2), (key212, 2), (key218, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key659, 2), (key663, 2)]

theorem rowCheck8035 : row8035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8035 := by decide +kernel

theorem rowEval8035 (x : Key → ℝ) : Integer.Sparse.eval row8035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8035, Integer.Sparse.eval_collectBalanced, rawRowCheck8035]

def rawRow8036 : Integer.Sparse Key := [(key105, -6), (key100, -6), (key137, -6), (key115, -6), (key48, 2), (key43, 2), (key74, 2), (key212, 2), (key206, 2), (key460, 2), (key426, 2), (key663, 2), (key659, 2), (key218, 2), (key490, 2), (key486, 2)]

theorem rawRowCheck8036 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form2 = rawRow8036 := by decide +kernel

def row8036 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key206, 2), (key212, 2), (key218, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key659, 2), (key663, 2)]

theorem rowCheck8036 : row8036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8036 := by decide +kernel

theorem rowEval8036 (x : Key → ℝ) : Integer.Sparse.eval row8036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8036, Integer.Sparse.eval_collectBalanced, rawRowCheck8036]

def rawRow8037 : Integer.Sparse Key := [(key100, -6), (key137, -6), (key105, -6), (key115, -6), (key43, 2), (key74, 2), (key48, 2), (key426, 2), (key659, 2), (key206, 2), (key663, 2), (key212, 2), (key460, 2), (key486, 2), (key218, 2), (key490, 2)]

theorem rawRowCheck8037 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form2 = rawRow8037 := by decide +kernel

def row8037 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key206, 2), (key212, 2), (key218, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key659, 2), (key663, 2)]

theorem rowCheck8037 : row8037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8037 := by decide +kernel

theorem rowEval8037 (x : Key → ℝ) : Integer.Sparse.eval row8037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8037, Integer.Sparse.eval_collectBalanced, rawRowCheck8037]

def rawRow8038 : Integer.Sparse Key := [(key137, -6), (key100, -6), (key105, -6), (key115, -6), (key74, 2), (key43, 2), (key48, 2), (key659, 2), (key426, 2), (key663, 2), (key206, 2), (key460, 2), (key212, 2), (key486, 2), (key490, 2), (key218, 2)]

theorem rawRowCheck8038 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form2 = rawRow8038 := by decide +kernel

def row8038 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key206, 2), (key212, 2), (key218, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key659, 2), (key663, 2)]

theorem rowCheck8038 : row8038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8038 := by decide +kernel

theorem rowEval8038 (x : Key → ℝ) : Integer.Sparse.eval row8038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8038, Integer.Sparse.eval_collectBalanced, rawRowCheck8038]

def rawRow8039 : Integer.Sparse Key := [(key105, -6), (key137, -6), (key100, -6), (key115, -6), (key48, 2), (key74, 2), (key43, 2), (key460, 2), (key663, 2), (key212, 2), (key659, 2), (key206, 2), (key426, 2), (key490, 2), (key218, 2), (key486, 2)]

theorem rawRowCheck8039 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form2 = rawRow8039 := by decide +kernel

def row8039 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key206, 2), (key212, 2), (key218, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key659, 2), (key663, 2)]

theorem rowCheck8039 : row8039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8039 := by decide +kernel

theorem rowEval8039 (x : Key → ℝ) : Integer.Sparse.eval row8039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8039, Integer.Sparse.eval_collectBalanced, rawRowCheck8039]

def rawRow8040 : Integer.Sparse Key := [(key137, -6), (key105, -6), (key100, -6), (key115, -6), (key74, 2), (key48, 2), (key43, 2), (key663, 2), (key460, 2), (key659, 2), (key212, 2), (key426, 2), (key206, 2), (key490, 2), (key486, 2), (key218, 2)]

theorem rawRowCheck8040 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form2 = rawRow8040 := by decide +kernel

def row8040 : Integer.Sparse Key := [(key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -6), (key137, -6), (key206, 2), (key212, 2), (key218, 2), (key426, 2), (key460, 2), (key486, 2), (key490, 2), (key659, 2), (key663, 2)]

theorem rowCheck8040 : row8040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8040 := by decide +kernel

theorem rowEval8040 (x : Key → ℝ) : Integer.Sparse.eval row8040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8040, Integer.Sparse.eval_collectBalanced, rawRowCheck8040]

def rawRow8041 : Integer.Sparse Key := [(key100, -6), (key115, -6), (key137, -6), (key105, -6), (key100, 2), (key115, 2), (key137, 2), (key18, 2), (key35, 2), (key375, 2), (key490, 2), (key654, 2), (key663, 2), (key212, 2), (key381, 2), (key460, 2)]

theorem rawRowCheck8041 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form2 = rawRow8041 := by decide +kernel

def row8041 : Integer.Sparse Key := [(key18, 2), (key35, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key212, 2), (key375, 2), (key381, 2), (key460, 2), (key490, 2), (key654, 2), (key663, 2)]

theorem rowCheck8041 : row8041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8041 := by decide +kernel

theorem rowEval8041 (x : Key → ℝ) : Integer.Sparse.eval row8041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8041, Integer.Sparse.eval_collectBalanced, rawRowCheck8041]

def rawRow8042 : Integer.Sparse Key := [(key115, -6), (key100, -6), (key137, -6), (key105, -6), (key115, 2), (key100, 2), (key137, 2), (key35, 2), (key18, 2), (key490, 2), (key375, 2), (key663, 2), (key654, 2), (key212, 2), (key460, 2), (key381, 2)]

theorem rawRowCheck8042 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form2 = rawRow8042 := by decide +kernel

def row8042 : Integer.Sparse Key := [(key18, 2), (key35, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key212, 2), (key375, 2), (key381, 2), (key460, 2), (key490, 2), (key654, 2), (key663, 2)]

theorem rowCheck8042 : row8042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8042 := by decide +kernel

theorem rowEval8042 (x : Key → ℝ) : Integer.Sparse.eval row8042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8042, Integer.Sparse.eval_collectBalanced, rawRowCheck8042]

def rawRow8043 : Integer.Sparse Key := [(key100, -6), (key137, -6), (key115, -6), (key105, -6), (key100, 2), (key137, 2), (key115, 2), (key43, 2), (key74, 2), (key206, 2), (key663, 2), (key218, 2), (key490, 2), (key381, 2), (key212, 2), (key460, 2)]

theorem rawRowCheck8043 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form2 = rawRow8043 := by decide +kernel

def row8043 : Integer.Sparse Key := [(key43, 2), (key74, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key206, 2), (key212, 2), (key218, 2), (key381, 2), (key460, 2), (key490, 2), (key663, 2)]

theorem rowCheck8043 : row8043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8043 := by decide +kernel

theorem rowEval8043 (x : Key → ℝ) : Integer.Sparse.eval row8043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8043, Integer.Sparse.eval_collectBalanced, rawRowCheck8043]

def rawRow8044 : Integer.Sparse Key := [(key137, -6), (key100, -6), (key115, -6), (key105, -6), (key137, 2), (key100, 2), (key115, 2), (key74, 2), (key43, 2), (key663, 2), (key206, 2), (key490, 2), (key218, 2), (key381, 2), (key460, 2), (key212, 2)]

theorem rawRowCheck8044 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form2 = rawRow8044 := by decide +kernel

def row8044 : Integer.Sparse Key := [(key43, 2), (key74, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key206, 2), (key212, 2), (key218, 2), (key381, 2), (key460, 2), (key490, 2), (key663, 2)]

theorem rowCheck8044 : row8044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8044 := by decide +kernel

theorem rowEval8044 (x : Key → ℝ) : Integer.Sparse.eval row8044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8044, Integer.Sparse.eval_collectBalanced, rawRowCheck8044]

def rawRow8045 : Integer.Sparse Key := [(key115, -6), (key137, -6), (key100, -6), (key105, -6), (key115, 2), (key137, 2), (key100, 2), (key196, 2), (key200, 2), (key35, 2), (key74, 2), (key18, 2), (key375, 2), (key460, 2), (key212, 2), (key381, 2)]

theorem rawRowCheck8045 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form2 = rawRow8045 := by decide +kernel

def row8045 : Integer.Sparse Key := [(key18, 2), (key35, 2), (key74, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key196, 2), (key200, 2), (key212, 2), (key375, 2), (key381, 2), (key460, 2)]

theorem rowCheck8045 : row8045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8045 := by decide +kernel

theorem rowEval8045 (x : Key → ℝ) : Integer.Sparse.eval row8045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8045, Integer.Sparse.eval_collectBalanced, rawRowCheck8045]

def rawRow8046 : Integer.Sparse Key := [(key137, -6), (key115, -6), (key100, -6), (key105, -6), (key137, 2), (key115, 2), (key100, 2), (key200, 2), (key196, 2), (key74, 2), (key35, 2), (key43, 2), (key206, 2), (key460, 2), (key381, 2), (key212, 2)]

theorem rawRowCheck8046 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form2 = rawRow8046 := by decide +kernel

def row8046 : Integer.Sparse Key := [(key35, 2), (key43, 2), (key74, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key196, 2), (key200, 2), (key206, 2), (key212, 2), (key381, 2), (key460, 2)]

theorem rowCheck8046 : row8046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8046 := by decide +kernel

theorem rowEval8046 (x : Key → ℝ) : Integer.Sparse.eval row8046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8046, Integer.Sparse.eval_collectBalanced, rawRowCheck8046]

def rawRow8047 : Integer.Sparse Key := [(key105, -6), (key115, -6), (key137, -6), (key100, -6), (key195, 2), (key196, 2), (key200, 2), (key23, 2), (key35, 2), (key48, 2), (key115, 2), (key74, 2), (key137, 2), (key18, 2), (key375, 2), (key426, 2)]

theorem rawRowCheck8047 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form2 = rawRow8047 := by decide +kernel

def row8047 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -4), (key137, -4), (key195, 2), (key196, 2), (key200, 2), (key375, 2), (key426, 2)]

theorem rowCheck8047 : row8047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8047 := by decide +kernel

theorem rowEval8047 (x : Key → ℝ) : Integer.Sparse.eval row8047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8047, Integer.Sparse.eval_collectBalanced, rawRowCheck8047]

def rawRow8048 : Integer.Sparse Key := [(key115, -6), (key105, -6), (key137, -6), (key100, -6), (key196, 2), (key195, 2), (key200, 2), (key35, 2), (key23, 2), (key115, 2), (key48, 2), (key137, 2), (key74, 2), (key18, 2), (key426, 2), (key375, 2)]

theorem rawRowCheck8048 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form2 = rawRow8048 := by decide +kernel

def row8048 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -4), (key137, -4), (key195, 2), (key196, 2), (key200, 2), (key375, 2), (key426, 2)]

theorem rowCheck8048 : row8048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8048 := by decide +kernel

theorem rowEval8048 (x : Key → ℝ) : Integer.Sparse.eval row8048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8048, Integer.Sparse.eval_collectBalanced, rawRowCheck8048]

def rawRow8049 : Integer.Sparse Key := [(key105, -6), (key137, -6), (key115, -6), (key100, -6), (key195, 2), (key200, 2), (key196, 2), (key48, 2), (key74, 2), (key23, 2), (key137, 2), (key35, 2), (key115, 2), (key43, 2), (key206, 2), (key426, 2)]

theorem rawRowCheck8049 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form2 = rawRow8049 := by decide +kernel

def row8049 : Integer.Sparse Key := [(key23, 2), (key35, 2), (key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -4), (key137, -4), (key195, 2), (key196, 2), (key200, 2), (key206, 2), (key426, 2)]

theorem rowCheck8049 : row8049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8049 := by decide +kernel

theorem rowEval8049 (x : Key → ℝ) : Integer.Sparse.eval row8049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck8049, Integer.Sparse.eval_collectBalanced, rawRowCheck8049]

def rawRow8050 : Integer.Sparse Key := [(key137, -6), (key105, -6), (key115, -6), (key100, -6), (key200, 2), (key195, 2), (key196, 2), (key74, 2), (key48, 2), (key137, 2), (key23, 2), (key115, 2), (key35, 2), (key43, 2), (key426, 2), (key206, 2)]

theorem rawRowCheck8050 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form2 = rawRow8050 := by decide +kernel

def row8050 : Integer.Sparse Key := [(key23, 2), (key35, 2), (key43, 2), (key48, 2), (key74, 2), (key100, -6), (key105, -6), (key115, -4), (key137, -4), (key195, 2), (key196, 2), (key200, 2), (key206, 2), (key426, 2)]

theorem rowCheck8050 : row8050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8050 := by decide +kernel

theorem rowEval8050 (x : Key → ℝ) : Integer.Sparse.eval row8050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8050, Integer.Sparse.eval_collectBalanced, rawRowCheck8050]

def rawRow8051 : Integer.Sparse Key := [(key115, -6), (key137, -6), (key105, -6), (key100, -6), (key196, 2), (key200, 2), (key195, 2), (key115, 2), (key137, 2), (key35, 2), (key74, 2), (key23, 2), (key48, 2), (key100, 2), (key18, 2), (key375, 2)]

theorem rawRowCheck8051 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form2 = rawRow8051 := by decide +kernel

def row8051 : Integer.Sparse Key := [(key18, 2), (key23, 2), (key35, 2), (key48, 2), (key74, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key195, 2), (key196, 2), (key200, 2), (key375, 2)]

theorem rowCheck8051 : row8051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8051 := by decide +kernel

theorem rowEval8051 (x : Key → ℝ) : Integer.Sparse.eval row8051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck8051, Integer.Sparse.eval_collectBalanced, rawRowCheck8051]

def rawRow8052 : Integer.Sparse Key := [(key137, -6), (key115, -6), (key105, -6), (key100, -6), (key200, 2), (key196, 2), (key195, 2), (key137, 2), (key115, 2), (key74, 2), (key35, 2), (key48, 2), (key23, 2), (key100, 2), (key43, 2), (key206, 2)]

theorem rawRowCheck8052 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form2 = rawRow8052 := by decide +kernel

def row8052 : Integer.Sparse Key := [(key23, 2), (key35, 2), (key43, 2), (key48, 2), (key74, 2), (key100, -4), (key105, -6), (key115, -4), (key137, -4), (key195, 2), (key196, 2), (key200, 2), (key206, 2)]

theorem rowCheck8052 : row8052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8052 := by decide +kernel

theorem rowEval8052 (x : Key → ℝ) : Integer.Sparse.eval row8052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck8052, Integer.Sparse.eval_collectBalanced, rawRowCheck8052]

def rawRow8053 : Integer.Sparse Key := [(key1293, -6), (key1570, -6), (key1570, -6), (key1590, -6), (key1313, 2), (key1313, 2), (key1323, 2), (key1421, 2), (key1421, 2), (key1441, 2), (key1619, 2), (key1621, 2), (key1619, 2), (key1630, 2), (key1621, 2), (key1630, 2)]

theorem rawRowCheck8053 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form3 = rawRow8053 := by decide +kernel

def row8053 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

theorem rowCheck8053 : row8053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8053 := by decide +kernel

theorem rowEval8053 (x : Key → ℝ) : Integer.Sparse.eval row8053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8053, Integer.Sparse.eval_collectBalanced, rawRowCheck8053]

def rawRow8054 : Integer.Sparse Key := [(key1293, -6), (key1570, -6), (key1590, -6), (key1570, -6), (key1313, 2), (key1323, 2), (key1313, 2), (key1421, 2), (key1441, 2), (key1421, 2), (key1621, 2), (key1619, 2), (key1630, 2), (key1619, 2), (key1630, 2), (key1621, 2)]

theorem rawRowCheck8054 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form3 = rawRow8054 := by decide +kernel

def row8054 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

theorem rowCheck8054 : row8054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8054 := by decide +kernel

theorem rowEval8054 (x : Key → ℝ) : Integer.Sparse.eval row8054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8054, Integer.Sparse.eval_collectBalanced, rawRowCheck8054]

def rawRow8055 : Integer.Sparse Key := [(key1293, -6), (key1590, -6), (key1570, -6), (key1570, -6), (key1323, 2), (key1313, 2), (key1313, 2), (key1441, 2), (key1421, 2), (key1421, 2), (key1630, 2), (key1630, 2), (key1621, 2), (key1621, 2), (key1619, 2), (key1619, 2)]

theorem rawRowCheck8055 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form3 = rawRow8055 := by decide +kernel

def row8055 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

theorem rowCheck8055 : row8055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8055 := by decide +kernel

theorem rowEval8055 (x : Key → ℝ) : Integer.Sparse.eval row8055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8055, Integer.Sparse.eval_collectBalanced, rawRowCheck8055]

def rawRow8056 : Integer.Sparse Key := [(key1570, -6), (key1293, -6), (key1570, -6), (key1590, -6), (key1421, 2), (key1619, 2), (key1621, 2), (key1313, 2), (key1619, 2), (key1630, 2), (key1313, 2), (key1323, 2), (key1421, 2), (key1441, 2), (key1621, 2), (key1630, 2)]

theorem rawRowCheck8056 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form3 = rawRow8056 := by decide +kernel

def row8056 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

theorem rowCheck8056 : row8056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8056 := by decide +kernel

theorem rowEval8056 (x : Key → ℝ) : Integer.Sparse.eval row8056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8056, Integer.Sparse.eval_collectBalanced, rawRowCheck8056]

def rawRow8057 : Integer.Sparse Key := [(key1570, -6), (key1293, -6), (key1590, -6), (key1570, -6), (key1421, 2), (key1621, 2), (key1619, 2), (key1313, 2), (key1630, 2), (key1619, 2), (key1323, 2), (key1313, 2), (key1441, 2), (key1421, 2), (key1630, 2), (key1621, 2)]

theorem rawRowCheck8057 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form3 = rawRow8057 := by decide +kernel

def row8057 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

theorem rowCheck8057 : row8057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8057 := by decide +kernel

theorem rowEval8057 (x : Key → ℝ) : Integer.Sparse.eval row8057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8057, Integer.Sparse.eval_collectBalanced, rawRowCheck8057]

def rawRow8058 : Integer.Sparse Key := [(key1570, -6), (key1570, -6), (key1293, -6), (key1590, -6), (key1619, 2), (key1421, 2), (key1621, 2), (key1619, 2), (key1313, 2), (key1630, 2), (key1421, 2), (key1621, 2), (key1313, 2), (key1630, 2), (key1323, 2), (key1441, 2)]

theorem rawRowCheck8058 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form3 = rawRow8058 := by decide +kernel

def row8058 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

theorem rowCheck8058 : row8058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8058 := by decide +kernel

theorem rowEval8058 (x : Key → ℝ) : Integer.Sparse.eval row8058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8058, Integer.Sparse.eval_collectBalanced, rawRowCheck8058]

def rawRow8059 : Integer.Sparse Key := [(key1570, -6), (key1570, -6), (key1590, -6), (key1293, -6), (key1619, 2), (key1621, 2), (key1421, 2), (key1619, 2), (key1630, 2), (key1313, 2), (key1621, 2), (key1421, 2), (key1630, 2), (key1313, 2), (key1441, 2), (key1323, 2)]

theorem rawRowCheck8059 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form3 = rawRow8059 := by decide +kernel

def row8059 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

theorem rowCheck8059 : row8059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8059 := by decide +kernel

theorem rowEval8059 (x : Key → ℝ) : Integer.Sparse.eval row8059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8059, Integer.Sparse.eval_collectBalanced, rawRowCheck8059]

def rawRow8060 : Integer.Sparse Key := [(key1570, -6), (key1590, -6), (key1293, -6), (key1570, -6), (key1621, 2), (key1421, 2), (key1619, 2), (key1630, 2), (key1313, 2), (key1619, 2), (key1441, 2), (key1630, 2), (key1323, 2), (key1621, 2), (key1313, 2), (key1421, 2)]

theorem rawRowCheck8060 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form3 = rawRow8060 := by decide +kernel

def row8060 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

theorem rowCheck8060 : row8060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8060 := by decide +kernel

theorem rowEval8060 (x : Key → ℝ) : Integer.Sparse.eval row8060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8060, Integer.Sparse.eval_collectBalanced, rawRowCheck8060]

def rawRow8061 : Integer.Sparse Key := [(key1570, -6), (key1590, -6), (key1570, -6), (key1293, -6), (key1621, 2), (key1619, 2), (key1421, 2), (key1630, 2), (key1619, 2), (key1313, 2), (key1630, 2), (key1441, 2), (key1621, 2), (key1323, 2), (key1421, 2), (key1313, 2)]

theorem rawRowCheck8061 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form3 = rawRow8061 := by decide +kernel

def row8061 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

theorem rowCheck8061 : row8061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8061 := by decide +kernel

theorem rowEval8061 (x : Key → ℝ) : Integer.Sparse.eval row8061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck8061, Integer.Sparse.eval_collectBalanced, rawRowCheck8061]

def rawRow8062 : Integer.Sparse Key := [(key1590, -6), (key1293, -6), (key1570, -6), (key1570, -6), (key1441, 2), (key1630, 2), (key1630, 2), (key1323, 2), (key1621, 2), (key1621, 2), (key1313, 2), (key1313, 2), (key1421, 2), (key1421, 2), (key1619, 2), (key1619, 2)]

theorem rawRowCheck8062 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form3 = rawRow8062 := by decide +kernel

def row8062 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

theorem rowCheck8062 : row8062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8062 := by decide +kernel

theorem rowEval8062 (x : Key → ℝ) : Integer.Sparse.eval row8062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8062, Integer.Sparse.eval_collectBalanced, rawRowCheck8062]

def rawRow8063 : Integer.Sparse Key := [(key1590, -6), (key1570, -6), (key1293, -6), (key1570, -6), (key1630, 2), (key1441, 2), (key1630, 2), (key1621, 2), (key1323, 2), (key1621, 2), (key1421, 2), (key1619, 2), (key1313, 2), (key1619, 2), (key1313, 2), (key1421, 2)]

theorem rawRowCheck8063 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form3 = rawRow8063 := by decide +kernel

def row8063 : Integer.Sparse Key := [(key1293, -6), (key1313, 4), (key1323, 2), (key1421, 4), (key1441, 2), (key1570, -12), (key1590, -6), (key1619, 4), (key1621, 4), (key1630, 4)]

theorem rowCheck8063 : row8063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow8063 := by decide +kernel

theorem rowEval8063 (x : Key → ℝ) : Integer.Sparse.eval row8063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck8063, Integer.Sparse.eval_collectBalanced, rawRowCheck8063]

end MUB6.Certificate.GramRows

end OAI
