import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow2048 : Integer.Sparse Key := [(key2847, -2), (key2847, -2), (key2890, -2), (key2878, 1), (key2881, 1), (key2878, 1), (key2911, 1), (key2881, 1), (key2911, 1), (key2591, 2), (key2591, 2), (key2601, 2), (key2878, -1), (key2911, -1), (key2878, -1), (key2990, -1), (key2911, -1), (key2990, -1), (key2591, -1), (key2594, -1), (key2591, -1), (key2601, -1), (key2594, -1), (key2601, -1), (key2847, 1), (key2890, 1), (key2847, 1), (key2969, 1), (key2890, 1), (key2969, 1)]

theorem rawRowCheck2048 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form9 = rawRow2048 := by decide +kernel

def row2048 : Integer.Sparse Key := [(key2591, 2), (key2594, -2), (key2847, -2), (key2881, 2), (key2969, 2), (key2990, -2)]

theorem rowCheck2048 : row2048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2048 := by decide +kernel

theorem rowEval2048 (x : Key → ℝ) : Integer.Sparse.eval row2048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form9) x := by
  rw [rowCheck2048, Integer.Sparse.eval_collectBalanced, rawRowCheck2048]

def rawRow2049 : Integer.Sparse Key := [(key2847, -2), (key2890, -2), (key2847, -2), (key2881, 1), (key2878, 1), (key2911, 1), (key2878, 1), (key2911, 1), (key2881, 1), (key2591, 2), (key2601, 2), (key2591, 2), (key2911, -1), (key2878, -1), (key2990, -1), (key2878, -1), (key2990, -1), (key2911, -1), (key2594, -1), (key2591, -1), (key2601, -1), (key2591, -1), (key2601, -1), (key2594, -1), (key2890, 1), (key2847, 1), (key2969, 1), (key2847, 1), (key2969, 1), (key2890, 1)]

theorem rawRowCheck2049 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form9 = rawRow2049 := by decide +kernel

def row2049 : Integer.Sparse Key := [(key2591, 2), (key2594, -2), (key2847, -2), (key2881, 2), (key2969, 2), (key2990, -2)]

theorem rowCheck2049 : row2049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2049 := by decide +kernel

theorem rowEval2049 (x : Key → ℝ) : Integer.Sparse.eval row2049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2049, Integer.Sparse.eval_collectBalanced, rawRowCheck2049]

def rawRow2050 : Integer.Sparse Key := [(key2890, -2), (key2847, -2), (key2847, -2), (key2911, 1), (key2911, 1), (key2881, 1), (key2881, 1), (key2878, 1), (key2878, 1), (key2601, 2), (key2591, 2), (key2591, 2), (key2990, -1), (key2990, -1), (key2911, -1), (key2911, -1), (key2878, -1), (key2878, -1), (key2601, -1), (key2601, -1), (key2594, -1), (key2594, -1), (key2591, -1), (key2591, -1), (key2969, 1), (key2969, 1), (key2890, 1), (key2890, 1), (key2847, 1), (key2847, 1)]

theorem rawRowCheck2050 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form9 = rawRow2050 := by decide +kernel

def row2050 : Integer.Sparse Key := [(key2591, 2), (key2594, -2), (key2847, -2), (key2881, 2), (key2969, 2), (key2990, -2)]

theorem rowCheck2050 : row2050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2050 := by decide +kernel

theorem rowEval2050 (x : Key → ℝ) : Integer.Sparse.eval row2050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2050, Integer.Sparse.eval_collectBalanced, rawRowCheck2050]

def rawRow2051 : Integer.Sparse Key := [(key2773, -2), (key2881, -2), (key2881, -2), (key2770, 1), (key2770, 1), (key2847, 1), (key2847, 1), (key2878, 1), (key2878, 1), (key2932, 2), (key2990, 2), (key2990, 2), (key2591, -1), (key2591, -1), (key2770, -1), (key2770, -1), (key2878, -1), (key2878, -1), (key2932, -1), (key2932, -1), (key2969, -1), (key2969, -1), (key2990, -1), (key2990, -1), (key2594, 1), (key2594, 1), (key2773, 1), (key2773, 1), (key2881, 1), (key2881, 1)]

theorem rawRowCheck2051 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form9 = rawRow2051 := by decide +kernel

def row2051 : Integer.Sparse Key := [(key2591, -2), (key2594, 2), (key2847, 2), (key2881, -2), (key2969, -2), (key2990, 2)]

theorem rowCheck2051 : row2051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2051 := by decide +kernel

theorem rowEval2051 (x : Key → ℝ) : Integer.Sparse.eval row2051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2051, Integer.Sparse.eval_collectBalanced, rawRowCheck2051]

def rawRow2052 : Integer.Sparse Key := [(key2881, -2), (key2773, -2), (key2881, -2), (key2847, 1), (key2878, 1), (key2770, 1), (key2878, 1), (key2770, 1), (key2847, 1), (key2990, 2), (key2932, 2), (key2990, 2), (key2770, -1), (key2878, -1), (key2591, -1), (key2878, -1), (key2591, -1), (key2770, -1), (key2969, -1), (key2990, -1), (key2932, -1), (key2990, -1), (key2932, -1), (key2969, -1), (key2773, 1), (key2881, 1), (key2594, 1), (key2881, 1), (key2594, 1), (key2773, 1)]

theorem rawRowCheck2052 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form9 = rawRow2052 := by decide +kernel

def row2052 : Integer.Sparse Key := [(key2591, -2), (key2594, 2), (key2847, 2), (key2881, -2), (key2969, -2), (key2990, 2)]

theorem rowCheck2052 : row2052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2052 := by decide +kernel

theorem rowEval2052 (x : Key → ℝ) : Integer.Sparse.eval row2052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2052, Integer.Sparse.eval_collectBalanced, rawRowCheck2052]

def rawRow2053 : Integer.Sparse Key := [(key2881, -2), (key2881, -2), (key2773, -2), (key2878, 1), (key2847, 1), (key2878, 1), (key2770, 1), (key2847, 1), (key2770, 1), (key2990, 2), (key2990, 2), (key2932, 2), (key2878, -1), (key2770, -1), (key2878, -1), (key2591, -1), (key2770, -1), (key2591, -1), (key2990, -1), (key2969, -1), (key2990, -1), (key2932, -1), (key2969, -1), (key2932, -1), (key2881, 1), (key2773, 1), (key2881, 1), (key2594, 1), (key2773, 1), (key2594, 1)]

theorem rawRowCheck2053 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form9 = rawRow2053 := by decide +kernel

def row2053 : Integer.Sparse Key := [(key2591, -2), (key2594, 2), (key2847, 2), (key2881, -2), (key2969, -2), (key2990, 2)]

theorem rowCheck2053 : row2053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2053 := by decide +kernel

theorem rowEval2053 (x : Key → ℝ) : Integer.Sparse.eval row2053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form9) x := by
  rw [rowCheck2053, Integer.Sparse.eval_collectBalanced, rawRowCheck2053]

def rawRow2054 : Integer.Sparse Key := [(key2969, -2), (key2969, -2), (key2969, -2), (key2990, 1), (key2990, 1), (key2990, 1), (key2990, 1), (key2990, 1), (key2990, 1), (key2594, 2), (key2594, 2), (key2594, 2), (key2881, -1), (key2881, -1), (key2881, -1), (key2881, -1), (key2881, -1), (key2881, -1), (key2591, -1), (key2591, -1), (key2591, -1), (key2591, -1), (key2591, -1), (key2591, -1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1), (key2847, 1)]

theorem rawRowCheck2054 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form9 = rawRow2054 := by decide +kernel

def row2054 : Integer.Sparse Key := [(key2591, -6), (key2594, 6), (key2847, 6), (key2881, -6), (key2969, -6), (key2990, 6)]

theorem rowCheck2054 : row2054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2054 := by decide +kernel

theorem rowEval2054 (x : Key → ℝ) : Integer.Sparse.eval row2054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2054, Integer.Sparse.eval_collectBalanced, rawRowCheck2054]

def rawRow2055 : Integer.Sparse Key := [(key2932, -2), (key2990, -2), (key2990, -2), (key2932, 1), (key2932, 1), (key2969, 1), (key2969, 1), (key2990, 1), (key2990, 1), (key2773, 2), (key2881, 2), (key2881, 2), (key2594, -1), (key2594, -1), (key2773, -1), (key2773, -1), (key2881, -1), (key2881, -1), (key2770, -1), (key2770, -1), (key2847, -1), (key2847, -1), (key2878, -1), (key2878, -1), (key2591, 1), (key2591, 1), (key2770, 1), (key2770, 1), (key2878, 1), (key2878, 1)]

theorem rawRowCheck2055 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form9 = rawRow2055 := by decide +kernel

def row2055 : Integer.Sparse Key := [(key2591, 2), (key2594, -2), (key2847, -2), (key2881, 2), (key2969, 2), (key2990, -2)]

theorem rowCheck2055 : row2055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2055 := by decide +kernel

theorem rowEval2055 (x : Key → ℝ) : Integer.Sparse.eval row2055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2055, Integer.Sparse.eval_collectBalanced, rawRowCheck2055]

def rawRow2056 : Integer.Sparse Key := [(key2990, -2), (key2932, -2), (key2990, -2), (key2969, 1), (key2990, 1), (key2932, 1), (key2990, 1), (key2932, 1), (key2969, 1), (key2881, 2), (key2773, 2), (key2881, 2), (key2773, -1), (key2881, -1), (key2594, -1), (key2881, -1), (key2594, -1), (key2773, -1), (key2847, -1), (key2878, -1), (key2770, -1), (key2878, -1), (key2770, -1), (key2847, -1), (key2770, 1), (key2878, 1), (key2591, 1), (key2878, 1), (key2591, 1), (key2770, 1)]

theorem rawRowCheck2056 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form9 = rawRow2056 := by decide +kernel

def row2056 : Integer.Sparse Key := [(key2591, 2), (key2594, -2), (key2847, -2), (key2881, 2), (key2969, 2), (key2990, -2)]

theorem rowCheck2056 : row2056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2056 := by decide +kernel

theorem rowEval2056 (x : Key → ℝ) : Integer.Sparse.eval row2056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form9) x := by
  rw [rowCheck2056, Integer.Sparse.eval_collectBalanced, rawRowCheck2056]

def rawRow2057 : Integer.Sparse Key := [(key2990, -2), (key2990, -2), (key2932, -2), (key2990, 1), (key2969, 1), (key2990, 1), (key2932, 1), (key2969, 1), (key2932, 1), (key2881, 2), (key2881, 2), (key2773, 2), (key2881, -1), (key2773, -1), (key2881, -1), (key2594, -1), (key2773, -1), (key2594, -1), (key2878, -1), (key2847, -1), (key2878, -1), (key2770, -1), (key2847, -1), (key2770, -1), (key2878, 1), (key2770, 1), (key2878, 1), (key2591, 1), (key2770, 1), (key2591, 1)]

theorem rawRowCheck2057 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form9 = rawRow2057 := by decide +kernel

def row2057 : Integer.Sparse Key := [(key2591, 2), (key2594, -2), (key2847, -2), (key2881, 2), (key2969, 2), (key2990, -2)]

theorem rowCheck2057 : row2057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2057 := by decide +kernel

theorem rowEval2057 (x : Key → ℝ) : Integer.Sparse.eval row2057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form9) x := by
  rw [rowCheck2057, Integer.Sparse.eval_collectBalanced, rawRowCheck2057]

def rawRow2058 : Integer.Sparse Key := [(key2354, -2), (key2358, -2), (key2358, -2), (key2358, 6), (key2449, 2), (key2453, 2), (key2453, 2), (key2453, -2), (key2453, -2), (key2529, -2), (key2514, -6), (key2514, 2), (key2514, 2), (key2559, 2)]

theorem rawRowCheck2058 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form10 = rawRow2058 := by decide +kernel

def row2058 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2514, -2), (key2529, -2), (key2559, 2)]

theorem rowCheck2058 : row2058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2058 := by decide +kernel

theorem rowEval2058 (x : Key → ℝ) : Integer.Sparse.eval row2058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2058, Integer.Sparse.eval_collectBalanced, rawRowCheck2058]

def rawRow2059 : Integer.Sparse Key := [(key2358, -2), (key2354, -2), (key2358, -2), (key2358, 6), (key2453, 2), (key2449, 2), (key2453, 2), (key2453, -2), (key2529, -2), (key2453, -2), (key2514, -6), (key2514, 2), (key2559, 2), (key2514, 2)]

theorem rawRowCheck2059 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form10 = rawRow2059 := by decide +kernel

def row2059 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2514, -2), (key2529, -2), (key2559, 2)]

theorem rowCheck2059 : row2059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2059 := by decide +kernel

theorem rowEval2059 (x : Key → ℝ) : Integer.Sparse.eval row2059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2059, Integer.Sparse.eval_collectBalanced, rawRowCheck2059]

def rawRow2060 : Integer.Sparse Key := [(key2358, -2), (key2358, -2), (key2354, -2), (key2358, 6), (key2453, 2), (key2453, 2), (key2449, 2), (key2529, -2), (key2453, -2), (key2453, -2), (key2514, -6), (key2559, 2), (key2514, 2), (key2514, 2)]

theorem rawRowCheck2060 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form10 = rawRow2060 := by decide +kernel

def row2060 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2514, -2), (key2529, -2), (key2559, 2)]

theorem rowCheck2060 : row2060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2060 := by decide +kernel

theorem rowEval2060 (x : Key → ℝ) : Integer.Sparse.eval row2060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2060, Integer.Sparse.eval_collectBalanced, rawRowCheck2060]

def rawRow2061 : Integer.Sparse Key := [(key2358, -2), (key2358, -2), (key2358, -2), (key2354, 6), (key2529, 2), (key2529, 2), (key2529, 2), (key2449, -2), (key2449, -2), (key2449, -2), (key2559, -6), (key2514, 2), (key2514, 2), (key2514, 2)]

theorem rawRowCheck2061 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form10 = rawRow2061 := by decide +kernel

def row2061 : Integer.Sparse Key := [(key2354, 6), (key2358, -6), (key2449, -6), (key2514, 6), (key2529, 6), (key2559, -6)]

theorem rowCheck2061 : row2061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2061 := by decide +kernel

theorem rowEval2061 (x : Key → ℝ) : Integer.Sparse.eval row2061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2061, Integer.Sparse.eval_collectBalanced, rawRowCheck2061]

def rawRow2062 : Integer.Sparse Key := [(key2449, -2), (key2453, -2), (key2453, -2), (key2514, 6), (key2354, 2), (key2358, 2), (key2358, 2), (key2514, -2), (key2514, -2), (key2559, -2), (key2358, -6), (key2453, 2), (key2453, 2), (key2529, 2)]

theorem rawRowCheck2062 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form10 = rawRow2062 := by decide +kernel

def row2062 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2514, 2), (key2529, 2), (key2559, -2)]

theorem rowCheck2062 : row2062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2062 := by decide +kernel

theorem rowEval2062 (x : Key → ℝ) : Integer.Sparse.eval row2062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form10) x := by
  rw [rowCheck2062, Integer.Sparse.eval_collectBalanced, rawRowCheck2062]

def rawRow2063 : Integer.Sparse Key := [(key2453, -2), (key2449, -2), (key2453, -2), (key2514, 6), (key2358, 2), (key2354, 2), (key2358, 2), (key2514, -2), (key2559, -2), (key2514, -2), (key2358, -6), (key2453, 2), (key2529, 2), (key2453, 2)]

theorem rawRowCheck2063 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form10 = rawRow2063 := by decide +kernel

def row2063 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2514, 2), (key2529, 2), (key2559, -2)]

theorem rowCheck2063 : row2063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2063 := by decide +kernel

theorem rowEval2063 (x : Key → ℝ) : Integer.Sparse.eval row2063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2063, Integer.Sparse.eval_collectBalanced, rawRowCheck2063]

def rawRow2064 : Integer.Sparse Key := [(key2453, -2), (key2453, -2), (key2449, -2), (key2514, 6), (key2358, 2), (key2358, 2), (key2354, 2), (key2559, -2), (key2514, -2), (key2514, -2), (key2358, -6), (key2529, 2), (key2453, 2), (key2453, 2)]

theorem rawRowCheck2064 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form10 = rawRow2064 := by decide +kernel

def row2064 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2514, 2), (key2529, 2), (key2559, -2)]

theorem rowCheck2064 : row2064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2064 := by decide +kernel

theorem rowEval2064 (x : Key → ℝ) : Integer.Sparse.eval row2064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2064, Integer.Sparse.eval_collectBalanced, rawRowCheck2064]

def rawRow2065 : Integer.Sparse Key := [(key2453, -2), (key2453, -2), (key2514, -2), (key2449, 6), (key2529, 2), (key2529, 2), (key2559, 2), (key2354, -2), (key2449, -2), (key2449, -2), (key2529, -6), (key2358, 2), (key2453, 2), (key2453, 2)]

theorem rawRowCheck2065 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form10 = rawRow2065 := by decide +kernel

def row2065 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2514, -2), (key2529, -2), (key2559, 2)]

theorem rowCheck2065 : row2065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2065 := by decide +kernel

theorem rowEval2065 (x : Key → ℝ) : Integer.Sparse.eval row2065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2065, Integer.Sparse.eval_collectBalanced, rawRowCheck2065]

def rawRow2066 : Integer.Sparse Key := [(key2453, -2), (key2514, -2), (key2453, -2), (key2449, 6), (key2529, 2), (key2559, 2), (key2529, 2), (key2449, -2), (key2354, -2), (key2449, -2), (key2529, -6), (key2453, 2), (key2358, 2), (key2453, 2)]

theorem rawRowCheck2066 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form10 = rawRow2066 := by decide +kernel

def row2066 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2514, -2), (key2529, -2), (key2559, 2)]

theorem rowCheck2066 : row2066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2066 := by decide +kernel

theorem rowEval2066 (x : Key → ℝ) : Integer.Sparse.eval row2066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2066, Integer.Sparse.eval_collectBalanced, rawRowCheck2066]

def rawRow2067 : Integer.Sparse Key := [(key2514, -2), (key2453, -2), (key2453, -2), (key2449, 6), (key2559, 2), (key2529, 2), (key2529, 2), (key2449, -2), (key2449, -2), (key2354, -2), (key2529, -6), (key2453, 2), (key2453, 2), (key2358, 2)]

theorem rawRowCheck2067 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form10 = rawRow2067 := by decide +kernel

def row2067 : Integer.Sparse Key := [(key2354, -2), (key2358, 2), (key2449, 2), (key2514, -2), (key2529, -2), (key2559, 2)]

theorem rowCheck2067 : row2067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2067 := by decide +kernel

theorem rowEval2067 (x : Key → ℝ) : Integer.Sparse.eval row2067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form10) x := by
  rw [rowCheck2067, Integer.Sparse.eval_collectBalanced, rawRowCheck2067]

def rawRow2068 : Integer.Sparse Key := [(key2529, -2), (key2529, -2), (key2529, -2), (key2559, 6), (key2358, 2), (key2358, 2), (key2358, 2), (key2514, -2), (key2514, -2), (key2514, -2), (key2354, -6), (key2449, 2), (key2449, 2), (key2449, 2)]

theorem rawRowCheck2068 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form10 = rawRow2068 := by decide +kernel

def row2068 : Integer.Sparse Key := [(key2354, -6), (key2358, 6), (key2449, 6), (key2514, -6), (key2529, -6), (key2559, 6)]

theorem rowCheck2068 : row2068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2068 := by decide +kernel

theorem rowEval2068 (x : Key → ℝ) : Integer.Sparse.eval row2068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2068, Integer.Sparse.eval_collectBalanced, rawRowCheck2068]

def rawRow2069 : Integer.Sparse Key := [(key2529, -2), (key2529, -2), (key2559, -2), (key2529, 6), (key2453, 2), (key2453, 2), (key2514, 2), (key2358, -2), (key2453, -2), (key2453, -2), (key2449, -6), (key2354, 2), (key2449, 2), (key2449, 2)]

theorem rawRowCheck2069 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form10 = rawRow2069 := by decide +kernel

def row2069 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2514, 2), (key2529, 2), (key2559, -2)]

theorem rowCheck2069 : row2069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2069 := by decide +kernel

theorem rowEval2069 (x : Key → ℝ) : Integer.Sparse.eval row2069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2069, Integer.Sparse.eval_collectBalanced, rawRowCheck2069]

def rawRow2070 : Integer.Sparse Key := [(key2529, -2), (key2559, -2), (key2529, -2), (key2529, 6), (key2453, 2), (key2514, 2), (key2453, 2), (key2453, -2), (key2358, -2), (key2453, -2), (key2449, -6), (key2449, 2), (key2354, 2), (key2449, 2)]

theorem rawRowCheck2070 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form10 = rawRow2070 := by decide +kernel

def row2070 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2514, 2), (key2529, 2), (key2559, -2)]

theorem rowCheck2070 : row2070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2070 := by decide +kernel

theorem rowEval2070 (x : Key → ℝ) : Integer.Sparse.eval row2070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form10) x := by
  rw [rowCheck2070, Integer.Sparse.eval_collectBalanced, rawRowCheck2070]

def rawRow2071 : Integer.Sparse Key := [(key2559, -2), (key2529, -2), (key2529, -2), (key2529, 6), (key2514, 2), (key2453, 2), (key2453, 2), (key2453, -2), (key2453, -2), (key2358, -2), (key2449, -6), (key2449, 2), (key2449, 2), (key2354, 2)]

theorem rawRowCheck2071 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form10 = rawRow2071 := by decide +kernel

def row2071 : Integer.Sparse Key := [(key2354, 2), (key2358, -2), (key2449, -2), (key2514, 2), (key2529, 2), (key2559, -2)]

theorem rowCheck2071 : row2071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2071 := by decide +kernel

theorem rowEval2071 (x : Key → ℝ) : Integer.Sparse.eval row2071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form10) x := by
  rw [rowCheck2071, Integer.Sparse.eval_collectBalanced, rawRowCheck2071]

def rawRow2072 : Integer.Sparse Key := [(key2353, -2), (key2356, -2), (key2356, -2), (key2356, 6), (key2448, 2), (key2451, 2), (key2451, 2), (key2451, -2), (key2451, -2), (key2513, -2), (key2527, -6), (key2527, 2), (key2527, 2), (key2558, 2)]

theorem rawRowCheck2072 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form11 = rawRow2072 := by decide +kernel

def row2072 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2513, -2), (key2527, -2), (key2558, 2)]

theorem rowCheck2072 : row2072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2072 := by decide +kernel

theorem rowEval2072 (x : Key → ℝ) : Integer.Sparse.eval row2072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2072, Integer.Sparse.eval_collectBalanced, rawRowCheck2072]

def rawRow2073 : Integer.Sparse Key := [(key2356, -2), (key2353, -2), (key2356, -2), (key2356, 6), (key2451, 2), (key2448, 2), (key2451, 2), (key2451, -2), (key2513, -2), (key2451, -2), (key2527, -6), (key2527, 2), (key2558, 2), (key2527, 2)]

theorem rawRowCheck2073 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form11 = rawRow2073 := by decide +kernel

def row2073 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2513, -2), (key2527, -2), (key2558, 2)]

theorem rowCheck2073 : row2073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2073 := by decide +kernel

theorem rowEval2073 (x : Key → ℝ) : Integer.Sparse.eval row2073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 0, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2073, Integer.Sparse.eval_collectBalanced, rawRowCheck2073]

def rawRow2074 : Integer.Sparse Key := [(key2356, -2), (key2356, -2), (key2353, -2), (key2356, 6), (key2451, 2), (key2451, 2), (key2448, 2), (key2513, -2), (key2451, -2), (key2451, -2), (key2527, -6), (key2558, 2), (key2527, 2), (key2527, 2)]

theorem rawRowCheck2074 : GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form11 = rawRow2074 := by decide +kernel

def row2074 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2513, -2), (key2527, -2), (key2558, 2)]

theorem rowCheck2074 : row2074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2074 := by decide +kernel

theorem rowEval2074 (x : Key → ℝ) : Integer.Sparse.eval row2074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 0, 1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2074, Integer.Sparse.eval_collectBalanced, rawRowCheck2074]

def rawRow2075 : Integer.Sparse Key := [(key2356, -2), (key2356, -2), (key2356, -2), (key2353, 6), (key2513, 2), (key2513, 2), (key2513, 2), (key2448, -2), (key2448, -2), (key2448, -2), (key2558, -6), (key2527, 2), (key2527, 2), (key2527, 2)]

theorem rawRowCheck2075 : GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form11 = rawRow2075 := by decide +kernel

def row2075 : Integer.Sparse Key := [(key2353, 6), (key2356, -6), (key2448, -6), (key2513, 6), (key2527, 6), (key2558, -6)]

theorem rowCheck2075 : row2075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2075 := by decide +kernel

theorem rowEval2075 (x : Key → ℝ) : Integer.Sparse.eval row2075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -3, 1, 0, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2075, Integer.Sparse.eval_collectBalanced, rawRowCheck2075]

def rawRow2076 : Integer.Sparse Key := [(key2448, -2), (key2451, -2), (key2451, -2), (key2513, 6), (key2353, 2), (key2356, 2), (key2356, 2), (key2527, -2), (key2527, -2), (key2558, -2), (key2356, -6), (key2451, 2), (key2451, 2), (key2513, 2)]

theorem rawRowCheck2076 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form11 = rawRow2076 := by decide +kernel

def row2076 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2513, 8), (key2527, -4), (key2558, -2)]

theorem rowCheck2076 : row2076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2076 := by decide +kernel

theorem rowEval2076 (x : Key → ℝ) : Integer.Sparse.eval row2076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 0, 1] GramFunctions.Block1.form11) x := by
  rw [rowCheck2076, Integer.Sparse.eval_collectBalanced, rawRowCheck2076]

def rawRow2077 : Integer.Sparse Key := [(key2451, -2), (key2448, -2), (key2451, -2), (key2513, 6), (key2356, 2), (key2353, 2), (key2356, 2), (key2527, -2), (key2558, -2), (key2527, -2), (key2356, -6), (key2451, 2), (key2513, 2), (key2451, 2)]

theorem rawRowCheck2077 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form11 = rawRow2077 := by decide +kernel

def row2077 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2513, 8), (key2527, -4), (key2558, -2)]

theorem rowCheck2077 : row2077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2077 := by decide +kernel

theorem rowEval2077 (x : Key → ℝ) : Integer.Sparse.eval row2077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 0, 1, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2077, Integer.Sparse.eval_collectBalanced, rawRowCheck2077]

def rawRow2078 : Integer.Sparse Key := [(key2451, -2), (key2451, -2), (key2448, -2), (key2513, 6), (key2356, 2), (key2356, 2), (key2353, 2), (key2558, -2), (key2527, -2), (key2527, -2), (key2356, -6), (key2513, 2), (key2451, 2), (key2451, 2)]

theorem rawRowCheck2078 : GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form11 = rawRow2078 := by decide +kernel

def row2078 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2513, 8), (key2527, -4), (key2558, -2)]

theorem rowCheck2078 : row2078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2078 := by decide +kernel

theorem rowEval2078 (x : Key → ℝ) : Integer.Sparse.eval row2078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -3, 1, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2078, Integer.Sparse.eval_collectBalanced, rawRowCheck2078]

def rawRow2079 : Integer.Sparse Key := [(key2451, -2), (key2451, -2), (key2513, -2), (key2448, 6), (key2527, 2), (key2527, 2), (key2558, 2), (key2353, -2), (key2448, -2), (key2448, -2), (key2513, -6), (key2356, 2), (key2451, 2), (key2451, 2)]

theorem rawRowCheck2079 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form11 = rawRow2079 := by decide +kernel

def row2079 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2513, -8), (key2527, 4), (key2558, 2)]

theorem rowCheck2079 : row2079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2079 := by decide +kernel

theorem rowEval2079 (x : Key → ℝ) : Integer.Sparse.eval row2079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -3, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2079, Integer.Sparse.eval_collectBalanced, rawRowCheck2079]

def rawRow2080 : Integer.Sparse Key := [(key2451, -2), (key2513, -2), (key2451, -2), (key2448, 6), (key2527, 2), (key2558, 2), (key2527, 2), (key2448, -2), (key2353, -2), (key2448, -2), (key2513, -6), (key2451, 2), (key2356, 2), (key2451, 2)]

theorem rawRowCheck2080 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form11 = rawRow2080 := by decide +kernel

def row2080 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2513, -8), (key2527, 4), (key2558, 2)]

theorem rowCheck2080 : row2080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2080 := by decide +kernel

theorem rowEval2080 (x : Key → ℝ) : Integer.Sparse.eval row2080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -3, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2080, Integer.Sparse.eval_collectBalanced, rawRowCheck2080]

def rawRow2081 : Integer.Sparse Key := [(key2513, -2), (key2451, -2), (key2451, -2), (key2448, 6), (key2558, 2), (key2527, 2), (key2527, 2), (key2448, -2), (key2448, -2), (key2353, -2), (key2513, -6), (key2451, 2), (key2451, 2), (key2356, 2)]

theorem rawRowCheck2081 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form11 = rawRow2081 := by decide +kernel

def row2081 : Integer.Sparse Key := [(key2353, -2), (key2356, 2), (key2448, 2), (key2513, -8), (key2527, 4), (key2558, 2)]

theorem rowCheck2081 : row2081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2081 := by decide +kernel

theorem rowEval2081 (x : Key → ℝ) : Integer.Sparse.eval row2081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, 0, -3] GramFunctions.Block1.form11) x := by
  rw [rowCheck2081, Integer.Sparse.eval_collectBalanced, rawRowCheck2081]

def rawRow2082 : Integer.Sparse Key := [(key2527, -2), (key2527, -2), (key2527, -2), (key2558, 6), (key2356, 2), (key2356, 2), (key2356, 2), (key2513, -2), (key2513, -2), (key2513, -2), (key2353, -6), (key2448, 2), (key2448, 2), (key2448, 2)]

theorem rawRowCheck2082 : GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form11 = rawRow2082 := by decide +kernel

def row2082 : Integer.Sparse Key := [(key2353, -6), (key2356, 6), (key2448, 6), (key2513, -6), (key2527, -6), (key2558, 6)]

theorem rowCheck2082 : row2082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2082 := by decide +kernel

theorem rowEval2082 (x : Key → ℝ) : Integer.Sparse.eval row2082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -3, 0, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2082, Integer.Sparse.eval_collectBalanced, rawRowCheck2082]

def rawRow2083 : Integer.Sparse Key := [(key2527, -2), (key2527, -2), (key2558, -2), (key2527, 6), (key2451, 2), (key2451, 2), (key2513, 2), (key2356, -2), (key2451, -2), (key2451, -2), (key2448, -6), (key2353, 2), (key2448, 2), (key2448, 2)]

theorem rawRowCheck2083 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form11 = rawRow2083 := by decide +kernel

def row2083 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2513, 2), (key2527, 2), (key2558, -2)]

theorem rowCheck2083 : row2083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2083 := by decide +kernel

theorem rowEval2083 (x : Key → ℝ) : Integer.Sparse.eval row2083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2083, Integer.Sparse.eval_collectBalanced, rawRowCheck2083]

def rawRow2084 : Integer.Sparse Key := [(key2527, -2), (key2558, -2), (key2527, -2), (key2527, 6), (key2451, 2), (key2513, 2), (key2451, 2), (key2451, -2), (key2356, -2), (key2451, -2), (key2448, -6), (key2448, 2), (key2353, 2), (key2448, 2)]

theorem rawRowCheck2084 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form11 = rawRow2084 := by decide +kernel

def row2084 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2513, 2), (key2527, 2), (key2558, -2)]

theorem rowCheck2084 : row2084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2084 := by decide +kernel

theorem rowEval2084 (x : Key → ℝ) : Integer.Sparse.eval row2084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -3, 0] GramFunctions.Block1.form11) x := by
  rw [rowCheck2084, Integer.Sparse.eval_collectBalanced, rawRowCheck2084]

def rawRow2085 : Integer.Sparse Key := [(key2558, -2), (key2527, -2), (key2527, -2), (key2527, 6), (key2513, 2), (key2451, 2), (key2451, 2), (key2451, -2), (key2451, -2), (key2356, -2), (key2448, -6), (key2448, 2), (key2448, 2), (key2353, 2)]

theorem rawRowCheck2085 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form11 = rawRow2085 := by decide +kernel

def row2085 : Integer.Sparse Key := [(key2353, 2), (key2356, -2), (key2448, -2), (key2513, 2), (key2527, 2), (key2558, -2)]

theorem rowCheck2085 : row2085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2085 := by decide +kernel

theorem rowEval2085 (x : Key → ℝ) : Integer.Sparse.eval row2085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, 0, -3] GramFunctions.Block1.form11) x := by
  rw [rowCheck2085, Integer.Sparse.eval_collectBalanced, rawRowCheck2085]

def rawRow2086 : Integer.Sparse Key := [(key2786, -2), (key2786, -2), (key2939, -2), (key2794, 1), (key2796, 1), (key2794, 1), (key2944, 1), (key2796, 1), (key2944, 1), (key2809, 2), (key2809, 2), (key2951, 2), (key2860, -1), (key2898, -1), (key2860, -1), (key2977, -1), (key2898, -1), (key2977, -1), (key2829, -1), (key2832, -1), (key2829, -1), (key2961, -1), (key2832, -1), (key2961, -1), (key2870, 1), (key2905, 1), (key2870, 1), (key2984, 1), (key2905, 1), (key2984, 1)]

theorem rawRowCheck2086 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form0 = rawRow2086 := by decide +kernel

def row2086 : Integer.Sparse Key := [(key2786, -4), (key2794, 2), (key2796, 2), (key2809, 4), (key2829, -2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

theorem rowCheck2086 : row2086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2086 := by decide +kernel

theorem rowEval2086 (x : Key → ℝ) : Integer.Sparse.eval row2086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2086, Integer.Sparse.eval_collectBalanced, rawRowCheck2086]

def rawRow2087 : Integer.Sparse Key := [(key2786, -2), (key2939, -2), (key2786, -2), (key2796, 1), (key2794, 1), (key2944, 1), (key2794, 1), (key2944, 1), (key2796, 1), (key2809, 2), (key2951, 2), (key2809, 2), (key2898, -1), (key2860, -1), (key2977, -1), (key2860, -1), (key2977, -1), (key2898, -1), (key2832, -1), (key2829, -1), (key2961, -1), (key2829, -1), (key2961, -1), (key2832, -1), (key2905, 1), (key2870, 1), (key2984, 1), (key2870, 1), (key2984, 1), (key2905, 1)]

theorem rawRowCheck2087 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form0 = rawRow2087 := by decide +kernel

def row2087 : Integer.Sparse Key := [(key2786, -4), (key2794, 2), (key2796, 2), (key2809, 4), (key2829, -2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

theorem rowCheck2087 : row2087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2087 := by decide +kernel

theorem rowEval2087 (x : Key → ℝ) : Integer.Sparse.eval row2087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2087, Integer.Sparse.eval_collectBalanced, rawRowCheck2087]

def rawRow2088 : Integer.Sparse Key := [(key2939, -2), (key2786, -2), (key2786, -2), (key2944, 1), (key2944, 1), (key2796, 1), (key2796, 1), (key2794, 1), (key2794, 1), (key2951, 2), (key2809, 2), (key2809, 2), (key2977, -1), (key2977, -1), (key2898, -1), (key2898, -1), (key2860, -1), (key2860, -1), (key2961, -1), (key2961, -1), (key2832, -1), (key2832, -1), (key2829, -1), (key2829, -1), (key2984, 1), (key2984, 1), (key2905, 1), (key2905, 1), (key2870, 1), (key2870, 1)]

theorem rawRowCheck2088 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form0 = rawRow2088 := by decide +kernel

def row2088 : Integer.Sparse Key := [(key2786, -4), (key2794, 2), (key2796, 2), (key2809, 4), (key2829, -2), (key2832, -2), (key2860, -2), (key2870, 2), (key2898, -2), (key2905, 2), (key2939, -2), (key2944, 2), (key2951, 2), (key2961, -2), (key2977, -2), (key2984, 2)]

theorem rowCheck2088 : row2088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2088 := by decide +kernel

theorem rowEval2088 (x : Key → ℝ) : Integer.Sparse.eval row2088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2088, Integer.Sparse.eval_collectBalanced, rawRowCheck2088]

def rawRow2089 : Integer.Sparse Key := [(key2671, -2), (key2794, -2), (key2944, -2), (key2671, 1), (key2674, 1), (key2786, 1), (key2939, 1), (key2796, 1), (key2944, 1), (key2706, 2), (key2860, 2), (key2977, 2), (key2706, -1), (key2738, -1), (key2809, -1), (key2951, -1), (key2898, -1), (key2977, -1), (key2726, -1), (key2729, -1), (key2870, -1), (key2984, -1), (key2883, -1), (key2992, -1), (key2726, 1), (key2748, 1), (key2829, 1), (key2961, 1), (key2913, 1), (key2992, 1)]

theorem rawRowCheck2089 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form0 = rawRow2089 := by decide +kernel

def row2089 : Integer.Sparse Key := [(key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, -1), (key2913, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck2089 : row2089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2089 := by decide +kernel

theorem rowEval2089 (x : Key → ℝ) : Integer.Sparse.eval row2089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2089, Integer.Sparse.eval_collectBalanced, rawRowCheck2089]

def rawRow2090 : Integer.Sparse Key := [(key2671, -2), (key2944, -2), (key2794, -2), (key2674, 1), (key2671, 1), (key2939, 1), (key2786, 1), (key2944, 1), (key2796, 1), (key2706, 2), (key2977, 2), (key2860, 2), (key2738, -1), (key2706, -1), (key2951, -1), (key2809, -1), (key2977, -1), (key2898, -1), (key2729, -1), (key2726, -1), (key2984, -1), (key2870, -1), (key2992, -1), (key2883, -1), (key2748, 1), (key2726, 1), (key2961, 1), (key2829, 1), (key2992, 1), (key2913, 1)]

theorem rawRowCheck2090 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form0 = rawRow2090 := by decide +kernel

def row2090 : Integer.Sparse Key := [(key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, -1), (key2913, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck2090 : row2090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2090 := by decide +kernel

theorem rowEval2090 (x : Key → ℝ) : Integer.Sparse.eval row2090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2090, Integer.Sparse.eval_collectBalanced, rawRowCheck2090]

def rawRow2091 : Integer.Sparse Key := [(key2794, -2), (key2671, -2), (key2944, -2), (key2786, 1), (key2796, 1), (key2671, 1), (key2944, 1), (key2674, 1), (key2939, 1), (key2860, 2), (key2706, 2), (key2977, 2), (key2809, -1), (key2898, -1), (key2706, -1), (key2977, -1), (key2738, -1), (key2951, -1), (key2870, -1), (key2883, -1), (key2726, -1), (key2992, -1), (key2729, -1), (key2984, -1), (key2829, 1), (key2913, 1), (key2726, 1), (key2992, 1), (key2748, 1), (key2961, 1)]

theorem rawRowCheck2091 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form0 = rawRow2091 := by decide +kernel

def row2091 : Integer.Sparse Key := [(key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, -1), (key2913, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck2091 : row2091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2091 := by decide +kernel

theorem rowEval2091 (x : Key → ℝ) : Integer.Sparse.eval row2091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2091, Integer.Sparse.eval_collectBalanced, rawRowCheck2091]

def rawRow2092 : Integer.Sparse Key := [(key2794, -2), (key2944, -2), (key2671, -2), (key2796, 1), (key2786, 1), (key2944, 1), (key2671, 1), (key2939, 1), (key2674, 1), (key2860, 2), (key2977, 2), (key2706, 2), (key2898, -1), (key2809, -1), (key2977, -1), (key2706, -1), (key2951, -1), (key2738, -1), (key2883, -1), (key2870, -1), (key2992, -1), (key2726, -1), (key2984, -1), (key2729, -1), (key2913, 1), (key2829, 1), (key2992, 1), (key2726, 1), (key2961, 1), (key2748, 1)]

theorem rawRowCheck2092 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form0 = rawRow2092 := by decide +kernel

def row2092 : Integer.Sparse Key := [(key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, -1), (key2913, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck2092 : row2092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2092 := by decide +kernel

theorem rowEval2092 (x : Key → ℝ) : Integer.Sparse.eval row2092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2092, Integer.Sparse.eval_collectBalanced, rawRowCheck2092]

def rawRow2093 : Integer.Sparse Key := [(key2944, -2), (key2671, -2), (key2794, -2), (key2939, 1), (key2944, 1), (key2674, 1), (key2796, 1), (key2671, 1), (key2786, 1), (key2977, 2), (key2706, 2), (key2860, 2), (key2951, -1), (key2977, -1), (key2738, -1), (key2898, -1), (key2706, -1), (key2809, -1), (key2984, -1), (key2992, -1), (key2729, -1), (key2883, -1), (key2726, -1), (key2870, -1), (key2961, 1), (key2992, 1), (key2748, 1), (key2913, 1), (key2726, 1), (key2829, 1)]

theorem rawRowCheck2093 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form0 = rawRow2093 := by decide +kernel

def row2093 : Integer.Sparse Key := [(key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, -1), (key2913, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck2093 : row2093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2093 := by decide +kernel

theorem rowEval2093 (x : Key → ℝ) : Integer.Sparse.eval row2093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2093, Integer.Sparse.eval_collectBalanced, rawRowCheck2093]

def rawRow2094 : Integer.Sparse Key := [(key2944, -2), (key2794, -2), (key2671, -2), (key2944, 1), (key2939, 1), (key2796, 1), (key2674, 1), (key2786, 1), (key2671, 1), (key2977, 2), (key2860, 2), (key2706, 2), (key2977, -1), (key2951, -1), (key2898, -1), (key2738, -1), (key2809, -1), (key2706, -1), (key2992, -1), (key2984, -1), (key2883, -1), (key2729, -1), (key2870, -1), (key2726, -1), (key2992, 1), (key2961, 1), (key2913, 1), (key2748, 1), (key2829, 1), (key2726, 1)]

theorem rawRowCheck2094 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form0 = rawRow2094 := by decide +kernel

def row2094 : Integer.Sparse Key := [(key2671, -1), (key2674, 1), (key2706, 1), (key2729, -1), (key2738, -1), (key2748, 1), (key2786, 1), (key2794, -2), (key2796, 1), (key2809, -1), (key2829, 1), (key2860, 2), (key2870, -1), (key2883, -1), (key2898, -1), (key2913, 1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck2094 : row2094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2094 := by decide +kernel

theorem rowEval2094 (x : Key → ℝ) : Integer.Sparse.eval row2094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2094, Integer.Sparse.eval_collectBalanced, rawRowCheck2094]

def rawRow2095 : Integer.Sparse Key := [(key2809, -2), (key2809, -2), (key2951, -2), (key2829, 1), (key2832, 1), (key2829, 1), (key2961, 1), (key2832, 1), (key2961, 1), (key2786, 2), (key2786, 2), (key2939, 2), (key2870, -1), (key2905, -1), (key2870, -1), (key2984, -1), (key2905, -1), (key2984, -1), (key2794, -1), (key2796, -1), (key2794, -1), (key2944, -1), (key2796, -1), (key2944, -1), (key2860, 1), (key2898, 1), (key2860, 1), (key2977, 1), (key2898, 1), (key2977, 1)]

theorem rawRowCheck2095 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form0 = rawRow2095 := by decide +kernel

def row2095 : Integer.Sparse Key := [(key2786, 4), (key2794, -2), (key2796, -2), (key2809, -4), (key2829, 2), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

theorem rowCheck2095 : row2095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2095 := by decide +kernel

theorem rowEval2095 (x : Key → ℝ) : Integer.Sparse.eval row2095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2095, Integer.Sparse.eval_collectBalanced, rawRowCheck2095]

def rawRow2096 : Integer.Sparse Key := [(key2809, -2), (key2951, -2), (key2809, -2), (key2832, 1), (key2829, 1), (key2961, 1), (key2829, 1), (key2961, 1), (key2832, 1), (key2786, 2), (key2939, 2), (key2786, 2), (key2905, -1), (key2870, -1), (key2984, -1), (key2870, -1), (key2984, -1), (key2905, -1), (key2796, -1), (key2794, -1), (key2944, -1), (key2794, -1), (key2944, -1), (key2796, -1), (key2898, 1), (key2860, 1), (key2977, 1), (key2860, 1), (key2977, 1), (key2898, 1)]

theorem rawRowCheck2096 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form0 = rawRow2096 := by decide +kernel

def row2096 : Integer.Sparse Key := [(key2786, 4), (key2794, -2), (key2796, -2), (key2809, -4), (key2829, 2), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

theorem rowCheck2096 : row2096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2096 := by decide +kernel

theorem rowEval2096 (x : Key → ℝ) : Integer.Sparse.eval row2096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2096, Integer.Sparse.eval_collectBalanced, rawRowCheck2096]

def rawRow2097 : Integer.Sparse Key := [(key2951, -2), (key2809, -2), (key2809, -2), (key2961, 1), (key2961, 1), (key2832, 1), (key2832, 1), (key2829, 1), (key2829, 1), (key2939, 2), (key2786, 2), (key2786, 2), (key2984, -1), (key2984, -1), (key2905, -1), (key2905, -1), (key2870, -1), (key2870, -1), (key2944, -1), (key2944, -1), (key2796, -1), (key2796, -1), (key2794, -1), (key2794, -1), (key2977, 1), (key2977, 1), (key2898, 1), (key2898, 1), (key2860, 1), (key2860, 1)]

theorem rawRowCheck2097 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form0 = rawRow2097 := by decide +kernel

def row2097 : Integer.Sparse Key := [(key2786, 4), (key2794, -2), (key2796, -2), (key2809, -4), (key2829, 2), (key2832, 2), (key2860, 2), (key2870, -2), (key2898, 2), (key2905, -2), (key2939, 2), (key2944, -2), (key2951, -2), (key2961, 2), (key2977, 2), (key2984, -2)]

theorem rowCheck2097 : row2097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2097 := by decide +kernel

theorem rowEval2097 (x : Key → ℝ) : Integer.Sparse.eval row2097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2097, Integer.Sparse.eval_collectBalanced, rawRowCheck2097]

def rawRow2098 : Integer.Sparse Key := [(key2616, -2), (key2829, -2), (key2961, -2), (key2616, 1), (key2619, 1), (key2809, 1), (key2951, 1), (key2832, 1), (key2961, 1), (key2632, 2), (key2870, 2), (key2984, 2), (key2632, -1), (key2649, -1), (key2786, -1), (key2939, -1), (key2905, -1), (key2984, -1), (key2640, -1), (key2642, -1), (key2860, -1), (key2977, -1), (key2883, -1), (key2992, -1), (key2640, 1), (key2654, 1), (key2794, 1), (key2944, 1), (key2913, 1), (key2992, 1)]

theorem rawRowCheck2098 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form0 = rawRow2098 := by decide +kernel

def row2098 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -2), (key2832, 1), (key2860, -1), (key2870, 2), (key2883, -1), (key2905, -1), (key2913, 1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck2098 : row2098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2098 := by decide +kernel

theorem rowEval2098 (x : Key → ℝ) : Integer.Sparse.eval row2098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2098, Integer.Sparse.eval_collectBalanced, rawRowCheck2098]

def rawRow2099 : Integer.Sparse Key := [(key2616, -2), (key2961, -2), (key2829, -2), (key2619, 1), (key2616, 1), (key2951, 1), (key2809, 1), (key2961, 1), (key2832, 1), (key2632, 2), (key2984, 2), (key2870, 2), (key2649, -1), (key2632, -1), (key2939, -1), (key2786, -1), (key2984, -1), (key2905, -1), (key2642, -1), (key2640, -1), (key2977, -1), (key2860, -1), (key2992, -1), (key2883, -1), (key2654, 1), (key2640, 1), (key2944, 1), (key2794, 1), (key2992, 1), (key2913, 1)]

theorem rawRowCheck2099 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form0 = rawRow2099 := by decide +kernel

def row2099 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -2), (key2832, 1), (key2860, -1), (key2870, 2), (key2883, -1), (key2905, -1), (key2913, 1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck2099 : row2099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2099 := by decide +kernel

theorem rowEval2099 (x : Key → ℝ) : Integer.Sparse.eval row2099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2099, Integer.Sparse.eval_collectBalanced, rawRowCheck2099]

def rawRow2100 : Integer.Sparse Key := [(key2829, -2), (key2616, -2), (key2961, -2), (key2809, 1), (key2832, 1), (key2616, 1), (key2961, 1), (key2619, 1), (key2951, 1), (key2870, 2), (key2632, 2), (key2984, 2), (key2786, -1), (key2905, -1), (key2632, -1), (key2984, -1), (key2649, -1), (key2939, -1), (key2860, -1), (key2883, -1), (key2640, -1), (key2992, -1), (key2642, -1), (key2977, -1), (key2794, 1), (key2913, 1), (key2640, 1), (key2992, 1), (key2654, 1), (key2944, 1)]

theorem rawRowCheck2100 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form0 = rawRow2100 := by decide +kernel

def row2100 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -2), (key2832, 1), (key2860, -1), (key2870, 2), (key2883, -1), (key2905, -1), (key2913, 1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck2100 : row2100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2100 := by decide +kernel

theorem rowEval2100 (x : Key → ℝ) : Integer.Sparse.eval row2100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2100, Integer.Sparse.eval_collectBalanced, rawRowCheck2100]

def rawRow2101 : Integer.Sparse Key := [(key2829, -2), (key2961, -2), (key2616, -2), (key2832, 1), (key2809, 1), (key2961, 1), (key2616, 1), (key2951, 1), (key2619, 1), (key2870, 2), (key2984, 2), (key2632, 2), (key2905, -1), (key2786, -1), (key2984, -1), (key2632, -1), (key2939, -1), (key2649, -1), (key2883, -1), (key2860, -1), (key2992, -1), (key2640, -1), (key2977, -1), (key2642, -1), (key2913, 1), (key2794, 1), (key2992, 1), (key2640, 1), (key2944, 1), (key2654, 1)]

theorem rawRowCheck2101 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form0 = rawRow2101 := by decide +kernel

def row2101 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -2), (key2832, 1), (key2860, -1), (key2870, 2), (key2883, -1), (key2905, -1), (key2913, 1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck2101 : row2101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2101 := by decide +kernel

theorem rowEval2101 (x : Key → ℝ) : Integer.Sparse.eval row2101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck2101, Integer.Sparse.eval_collectBalanced, rawRowCheck2101]

def rawRow2102 : Integer.Sparse Key := [(key2961, -2), (key2616, -2), (key2829, -2), (key2951, 1), (key2961, 1), (key2619, 1), (key2832, 1), (key2616, 1), (key2809, 1), (key2984, 2), (key2632, 2), (key2870, 2), (key2939, -1), (key2984, -1), (key2649, -1), (key2905, -1), (key2632, -1), (key2786, -1), (key2977, -1), (key2992, -1), (key2642, -1), (key2883, -1), (key2640, -1), (key2860, -1), (key2944, 1), (key2992, 1), (key2654, 1), (key2913, 1), (key2640, 1), (key2794, 1)]

theorem rawRowCheck2102 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form0 = rawRow2102 := by decide +kernel

def row2102 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -2), (key2832, 1), (key2860, -1), (key2870, 2), (key2883, -1), (key2905, -1), (key2913, 1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck2102 : row2102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2102 := by decide +kernel

theorem rowEval2102 (x : Key → ℝ) : Integer.Sparse.eval row2102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2102, Integer.Sparse.eval_collectBalanced, rawRowCheck2102]

def rawRow2103 : Integer.Sparse Key := [(key2961, -2), (key2829, -2), (key2616, -2), (key2961, 1), (key2951, 1), (key2832, 1), (key2619, 1), (key2809, 1), (key2616, 1), (key2984, 2), (key2870, 2), (key2632, 2), (key2984, -1), (key2939, -1), (key2905, -1), (key2649, -1), (key2786, -1), (key2632, -1), (key2992, -1), (key2977, -1), (key2883, -1), (key2642, -1), (key2860, -1), (key2640, -1), (key2992, 1), (key2944, 1), (key2913, 1), (key2654, 1), (key2794, 1), (key2640, 1)]

theorem rawRowCheck2103 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form0 = rawRow2103 := by decide +kernel

def row2103 : Integer.Sparse Key := [(key2616, -1), (key2619, 1), (key2632, 1), (key2642, -1), (key2649, -1), (key2654, 1), (key2786, -1), (key2794, 1), (key2809, 1), (key2829, -2), (key2832, 1), (key2860, -1), (key2870, 2), (key2883, -1), (key2905, -1), (key2913, 1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck2103 : row2103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2103 := by decide +kernel

theorem rowEval2103 (x : Key → ℝ) : Integer.Sparse.eval row2103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck2103, Integer.Sparse.eval_collectBalanced, rawRowCheck2103]

def rawRow2104 : Integer.Sparse Key := [(key2706, -2), (key2860, -2), (key2977, -2), (key2726, 1), (key2729, 1), (key2870, 1), (key2984, 1), (key2883, 1), (key2992, 1), (key2671, 2), (key2794, 2), (key2944, 2), (key2726, -1), (key2748, -1), (key2829, -1), (key2961, -1), (key2913, -1), (key2992, -1), (key2671, -1), (key2674, -1), (key2786, -1), (key2939, -1), (key2796, -1), (key2944, -1), (key2706, 1), (key2738, 1), (key2809, 1), (key2951, 1), (key2898, 1), (key2977, 1)]

theorem rawRowCheck2104 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form0 = rawRow2104 := by decide +kernel

def row2104 : Integer.Sparse Key := [(key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2794, 2), (key2796, -1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, 1), (key2913, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck2104 : row2104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2104 := by decide +kernel

theorem rowEval2104 (x : Key → ℝ) : Integer.Sparse.eval row2104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2104, Integer.Sparse.eval_collectBalanced, rawRowCheck2104]

def rawRow2105 : Integer.Sparse Key := [(key2706, -2), (key2977, -2), (key2860, -2), (key2729, 1), (key2726, 1), (key2984, 1), (key2870, 1), (key2992, 1), (key2883, 1), (key2671, 2), (key2944, 2), (key2794, 2), (key2748, -1), (key2726, -1), (key2961, -1), (key2829, -1), (key2992, -1), (key2913, -1), (key2674, -1), (key2671, -1), (key2939, -1), (key2786, -1), (key2944, -1), (key2796, -1), (key2738, 1), (key2706, 1), (key2951, 1), (key2809, 1), (key2977, 1), (key2898, 1)]

theorem rawRowCheck2105 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form0 = rawRow2105 := by decide +kernel

def row2105 : Integer.Sparse Key := [(key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2794, 2), (key2796, -1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, 1), (key2913, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck2105 : row2105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2105 := by decide +kernel

theorem rowEval2105 (x : Key → ℝ) : Integer.Sparse.eval row2105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2105, Integer.Sparse.eval_collectBalanced, rawRowCheck2105]

def rawRow2106 : Integer.Sparse Key := [(key2860, -2), (key2706, -2), (key2977, -2), (key2870, 1), (key2883, 1), (key2726, 1), (key2992, 1), (key2729, 1), (key2984, 1), (key2794, 2), (key2671, 2), (key2944, 2), (key2829, -1), (key2913, -1), (key2726, -1), (key2992, -1), (key2748, -1), (key2961, -1), (key2786, -1), (key2796, -1), (key2671, -1), (key2944, -1), (key2674, -1), (key2939, -1), (key2809, 1), (key2898, 1), (key2706, 1), (key2977, 1), (key2738, 1), (key2951, 1)]

theorem rawRowCheck2106 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form0 = rawRow2106 := by decide +kernel

def row2106 : Integer.Sparse Key := [(key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2794, 2), (key2796, -1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, 1), (key2913, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck2106 : row2106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2106 := by decide +kernel

theorem rowEval2106 (x : Key → ℝ) : Integer.Sparse.eval row2106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2106, Integer.Sparse.eval_collectBalanced, rawRowCheck2106]

def rawRow2107 : Integer.Sparse Key := [(key2860, -2), (key2977, -2), (key2706, -2), (key2883, 1), (key2870, 1), (key2992, 1), (key2726, 1), (key2984, 1), (key2729, 1), (key2794, 2), (key2944, 2), (key2671, 2), (key2913, -1), (key2829, -1), (key2992, -1), (key2726, -1), (key2961, -1), (key2748, -1), (key2796, -1), (key2786, -1), (key2944, -1), (key2671, -1), (key2939, -1), (key2674, -1), (key2898, 1), (key2809, 1), (key2977, 1), (key2706, 1), (key2951, 1), (key2738, 1)]

theorem rawRowCheck2107 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form0 = rawRow2107 := by decide +kernel

def row2107 : Integer.Sparse Key := [(key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2794, 2), (key2796, -1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, 1), (key2913, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck2107 : row2107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2107 := by decide +kernel

theorem rowEval2107 (x : Key → ℝ) : Integer.Sparse.eval row2107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2107, Integer.Sparse.eval_collectBalanced, rawRowCheck2107]

def rawRow2108 : Integer.Sparse Key := [(key2977, -2), (key2706, -2), (key2860, -2), (key2984, 1), (key2992, 1), (key2729, 1), (key2883, 1), (key2726, 1), (key2870, 1), (key2944, 2), (key2671, 2), (key2794, 2), (key2961, -1), (key2992, -1), (key2748, -1), (key2913, -1), (key2726, -1), (key2829, -1), (key2939, -1), (key2944, -1), (key2674, -1), (key2796, -1), (key2671, -1), (key2786, -1), (key2951, 1), (key2977, 1), (key2738, 1), (key2898, 1), (key2706, 1), (key2809, 1)]

theorem rawRowCheck2108 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form0 = rawRow2108 := by decide +kernel

def row2108 : Integer.Sparse Key := [(key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2794, 2), (key2796, -1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, 1), (key2913, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck2108 : row2108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2108 := by decide +kernel

theorem rowEval2108 (x : Key → ℝ) : Integer.Sparse.eval row2108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2108, Integer.Sparse.eval_collectBalanced, rawRowCheck2108]

def rawRow2109 : Integer.Sparse Key := [(key2977, -2), (key2860, -2), (key2706, -2), (key2992, 1), (key2984, 1), (key2883, 1), (key2729, 1), (key2870, 1), (key2726, 1), (key2944, 2), (key2794, 2), (key2671, 2), (key2992, -1), (key2961, -1), (key2913, -1), (key2748, -1), (key2829, -1), (key2726, -1), (key2944, -1), (key2939, -1), (key2796, -1), (key2674, -1), (key2786, -1), (key2671, -1), (key2977, 1), (key2951, 1), (key2898, 1), (key2738, 1), (key2809, 1), (key2706, 1)]

theorem rawRowCheck2109 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form0 = rawRow2109 := by decide +kernel

def row2109 : Integer.Sparse Key := [(key2671, 1), (key2674, -1), (key2706, -1), (key2729, 1), (key2738, 1), (key2748, -1), (key2786, -1), (key2794, 2), (key2796, -1), (key2809, 1), (key2829, -1), (key2860, -2), (key2870, 1), (key2883, 1), (key2898, 1), (key2913, -1), (key2939, -1), (key2944, 1), (key2951, 1), (key2961, -1), (key2977, -1), (key2984, 1)]

theorem rowCheck2109 : row2109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2109 := by decide +kernel

theorem rowEval2109 (x : Key → ℝ) : Integer.Sparse.eval row2109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2109, Integer.Sparse.eval_collectBalanced, rawRowCheck2109]

def rawRow2110 : Integer.Sparse Key := [(key2632, -2), (key2870, -2), (key2984, -2), (key2640, 1), (key2642, 1), (key2860, 1), (key2977, 1), (key2883, 1), (key2992, 1), (key2616, 2), (key2829, 2), (key2961, 2), (key2640, -1), (key2654, -1), (key2794, -1), (key2944, -1), (key2913, -1), (key2992, -1), (key2616, -1), (key2619, -1), (key2809, -1), (key2951, -1), (key2832, -1), (key2961, -1), (key2632, 1), (key2649, 1), (key2786, 1), (key2939, 1), (key2905, 1), (key2984, 1)]

theorem rawRowCheck2110 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form0 = rawRow2110 := by decide +kernel

def row2110 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2786, 1), (key2794, -1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -2), (key2883, 1), (key2905, 1), (key2913, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck2110 : row2110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2110 := by decide +kernel

theorem rowEval2110 (x : Key → ℝ) : Integer.Sparse.eval row2110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2110, Integer.Sparse.eval_collectBalanced, rawRowCheck2110]

def rawRow2111 : Integer.Sparse Key := [(key2632, -2), (key2984, -2), (key2870, -2), (key2642, 1), (key2640, 1), (key2977, 1), (key2860, 1), (key2992, 1), (key2883, 1), (key2616, 2), (key2961, 2), (key2829, 2), (key2654, -1), (key2640, -1), (key2944, -1), (key2794, -1), (key2992, -1), (key2913, -1), (key2619, -1), (key2616, -1), (key2951, -1), (key2809, -1), (key2961, -1), (key2832, -1), (key2649, 1), (key2632, 1), (key2939, 1), (key2786, 1), (key2984, 1), (key2905, 1)]

theorem rawRowCheck2111 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form0 = rawRow2111 := by decide +kernel

def row2111 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2786, 1), (key2794, -1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -2), (key2883, 1), (key2905, 1), (key2913, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck2111 : row2111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2111 := by decide +kernel

theorem rowEval2111 (x : Key → ℝ) : Integer.Sparse.eval row2111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2111, Integer.Sparse.eval_collectBalanced, rawRowCheck2111]

def rawRow2112 : Integer.Sparse Key := [(key2870, -2), (key2632, -2), (key2984, -2), (key2860, 1), (key2883, 1), (key2640, 1), (key2992, 1), (key2642, 1), (key2977, 1), (key2829, 2), (key2616, 2), (key2961, 2), (key2794, -1), (key2913, -1), (key2640, -1), (key2992, -1), (key2654, -1), (key2944, -1), (key2809, -1), (key2832, -1), (key2616, -1), (key2961, -1), (key2619, -1), (key2951, -1), (key2786, 1), (key2905, 1), (key2632, 1), (key2984, 1), (key2649, 1), (key2939, 1)]

theorem rawRowCheck2112 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form0 = rawRow2112 := by decide +kernel

def row2112 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2786, 1), (key2794, -1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -2), (key2883, 1), (key2905, 1), (key2913, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck2112 : row2112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2112 := by decide +kernel

theorem rowEval2112 (x : Key → ℝ) : Integer.Sparse.eval row2112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form0) x := by
  rw [rowCheck2112, Integer.Sparse.eval_collectBalanced, rawRowCheck2112]

def rawRow2113 : Integer.Sparse Key := [(key2870, -2), (key2984, -2), (key2632, -2), (key2883, 1), (key2860, 1), (key2992, 1), (key2640, 1), (key2977, 1), (key2642, 1), (key2829, 2), (key2961, 2), (key2616, 2), (key2913, -1), (key2794, -1), (key2992, -1), (key2640, -1), (key2944, -1), (key2654, -1), (key2832, -1), (key2809, -1), (key2961, -1), (key2616, -1), (key2951, -1), (key2619, -1), (key2905, 1), (key2786, 1), (key2984, 1), (key2632, 1), (key2939, 1), (key2649, 1)]

theorem rawRowCheck2113 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form0 = rawRow2113 := by decide +kernel

def row2113 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2786, 1), (key2794, -1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -2), (key2883, 1), (key2905, 1), (key2913, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck2113 : row2113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2113 := by decide +kernel

theorem rowEval2113 (x : Key → ℝ) : Integer.Sparse.eval row2113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck2113, Integer.Sparse.eval_collectBalanced, rawRowCheck2113]

def rawRow2114 : Integer.Sparse Key := [(key2984, -2), (key2632, -2), (key2870, -2), (key2977, 1), (key2992, 1), (key2642, 1), (key2883, 1), (key2640, 1), (key2860, 1), (key2961, 2), (key2616, 2), (key2829, 2), (key2944, -1), (key2992, -1), (key2654, -1), (key2913, -1), (key2640, -1), (key2794, -1), (key2951, -1), (key2961, -1), (key2619, -1), (key2832, -1), (key2616, -1), (key2809, -1), (key2939, 1), (key2984, 1), (key2649, 1), (key2905, 1), (key2632, 1), (key2786, 1)]

theorem rawRowCheck2114 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form0 = rawRow2114 := by decide +kernel

def row2114 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2786, 1), (key2794, -1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -2), (key2883, 1), (key2905, 1), (key2913, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck2114 : row2114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2114 := by decide +kernel

theorem rowEval2114 (x : Key → ℝ) : Integer.Sparse.eval row2114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form0) x := by
  rw [rowCheck2114, Integer.Sparse.eval_collectBalanced, rawRowCheck2114]

def rawRow2115 : Integer.Sparse Key := [(key2984, -2), (key2870, -2), (key2632, -2), (key2992, 1), (key2977, 1), (key2883, 1), (key2642, 1), (key2860, 1), (key2640, 1), (key2961, 2), (key2829, 2), (key2616, 2), (key2992, -1), (key2944, -1), (key2913, -1), (key2654, -1), (key2794, -1), (key2640, -1), (key2961, -1), (key2951, -1), (key2832, -1), (key2619, -1), (key2809, -1), (key2616, -1), (key2984, 1), (key2939, 1), (key2905, 1), (key2649, 1), (key2786, 1), (key2632, 1)]

theorem rawRowCheck2115 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form0 = rawRow2115 := by decide +kernel

def row2115 : Integer.Sparse Key := [(key2616, 1), (key2619, -1), (key2632, -1), (key2642, 1), (key2649, 1), (key2654, -1), (key2786, 1), (key2794, -1), (key2809, -1), (key2829, 2), (key2832, -1), (key2860, 1), (key2870, -2), (key2883, 1), (key2905, 1), (key2913, -1), (key2939, 1), (key2944, -1), (key2951, -1), (key2961, 1), (key2977, 1), (key2984, -1)]

theorem rowCheck2115 : row2115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2115 := by decide +kernel

theorem rowEval2115 (x : Key → ℝ) : Integer.Sparse.eval row2115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form0) x := by
  rw [rowCheck2115, Integer.Sparse.eval_collectBalanced, rawRowCheck2115]

def rawRow2116 : Integer.Sparse Key := [(key1288, -6), (key1308, 2), (key1308, 2), (key1334, 2), (key1383, 6), (key1538, -2), (key1538, -2), (key1769, -2), (key1416, -2), (key1416, -2), (key1452, -2), (key1565, 2), (key1565, 2), (key1785, 2)]

theorem rawRowCheck2116 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form1 = rawRow2116 := by decide +kernel

def row2116 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1383, 6), (key1416, -4), (key1452, -2), (key1538, -4), (key1565, 4), (key1769, -2), (key1785, 2)]

theorem rowCheck2116 : row2116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2116 := by decide +kernel

theorem rowEval2116 (x : Key → ℝ) : Integer.Sparse.eval row2116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2116, Integer.Sparse.eval_collectBalanced, rawRowCheck2116]

def rawRow2117 : Integer.Sparse Key := [(key1288, -6), (key1308, 2), (key1334, 2), (key1308, 2), (key1383, 6), (key1538, -2), (key1769, -2), (key1538, -2), (key1416, -2), (key1452, -2), (key1416, -2), (key1565, 2), (key1785, 2), (key1565, 2)]

theorem rawRowCheck2117 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form1 = rawRow2117 := by decide +kernel

def row2117 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1383, 6), (key1416, -4), (key1452, -2), (key1538, -4), (key1565, 4), (key1769, -2), (key1785, 2)]

theorem rowCheck2117 : row2117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2117 := by decide +kernel

theorem rowEval2117 (x : Key → ℝ) : Integer.Sparse.eval row2117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2117, Integer.Sparse.eval_collectBalanced, rawRowCheck2117]

def rawRow2118 : Integer.Sparse Key := [(key1288, -6), (key1334, 2), (key1308, 2), (key1308, 2), (key1383, 6), (key1769, -2), (key1538, -2), (key1538, -2), (key1452, -2), (key1416, -2), (key1416, -2), (key1785, 2), (key1565, 2), (key1565, 2)]

theorem rawRowCheck2118 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form1 = rawRow2118 := by decide +kernel

def row2118 : Integer.Sparse Key := [(key1288, -6), (key1308, 4), (key1334, 2), (key1383, 6), (key1416, -4), (key1452, -2), (key1538, -4), (key1565, 4), (key1769, -2), (key1785, 2)]

theorem rowCheck2118 : row2118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2118 := by decide +kernel

theorem rowEval2118 (x : Key → ℝ) : Integer.Sparse.eval row2118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2118, Integer.Sparse.eval_collectBalanced, rawRowCheck2118]

def rawRow2119 : Integer.Sparse Key := [(key1308, -6), (key1288, 2), (key1308, 2), (key1334, 2), (key1538, 6), (key1383, -2), (key1538, -2), (key1769, -2), (key1565, -2), (key1614, -2), (key1652, -2), (key1416, 2), (key1614, 2), (key1810, 2)]

theorem rawRowCheck2119 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form1 = rawRow2119 := by decide +kernel

def row2119 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, -2), (key1416, 2), (key1538, 4), (key1565, -2), (key1652, -2), (key1769, -2), (key1810, 2)]

theorem rowCheck2119 : row2119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2119 := by decide +kernel

theorem rowEval2119 (x : Key → ℝ) : Integer.Sparse.eval row2119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2119, Integer.Sparse.eval_collectBalanced, rawRowCheck2119]

def rawRow2120 : Integer.Sparse Key := [(key1308, -6), (key1288, 2), (key1334, 2), (key1308, 2), (key1538, 6), (key1383, -2), (key1769, -2), (key1538, -2), (key1565, -2), (key1652, -2), (key1614, -2), (key1416, 2), (key1810, 2), (key1614, 2)]

theorem rawRowCheck2120 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form1 = rawRow2120 := by decide +kernel

def row2120 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, -2), (key1416, 2), (key1538, 4), (key1565, -2), (key1652, -2), (key1769, -2), (key1810, 2)]

theorem rowCheck2120 : row2120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2120 := by decide +kernel

theorem rowEval2120 (x : Key → ℝ) : Integer.Sparse.eval row2120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2120, Integer.Sparse.eval_collectBalanced, rawRowCheck2120]

def rawRow2121 : Integer.Sparse Key := [(key1308, -6), (key1308, 2), (key1288, 2), (key1334, 2), (key1538, 6), (key1538, -2), (key1383, -2), (key1769, -2), (key1614, -2), (key1565, -2), (key1652, -2), (key1614, 2), (key1416, 2), (key1810, 2)]

theorem rawRowCheck2121 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form1 = rawRow2121 := by decide +kernel

def row2121 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, -2), (key1416, 2), (key1538, 4), (key1565, -2), (key1652, -2), (key1769, -2), (key1810, 2)]

theorem rowCheck2121 : row2121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2121 := by decide +kernel

theorem rowEval2121 (x : Key → ℝ) : Integer.Sparse.eval row2121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2121, Integer.Sparse.eval_collectBalanced, rawRowCheck2121]

def rawRow2122 : Integer.Sparse Key := [(key1308, -6), (key1308, 2), (key1334, 2), (key1288, 2), (key1538, 6), (key1538, -2), (key1769, -2), (key1383, -2), (key1614, -2), (key1652, -2), (key1565, -2), (key1614, 2), (key1810, 2), (key1416, 2)]

theorem rawRowCheck2122 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form1 = rawRow2122 := by decide +kernel

def row2122 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, -2), (key1416, 2), (key1538, 4), (key1565, -2), (key1652, -2), (key1769, -2), (key1810, 2)]

theorem rowCheck2122 : row2122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2122 := by decide +kernel

theorem rowEval2122 (x : Key → ℝ) : Integer.Sparse.eval row2122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2122, Integer.Sparse.eval_collectBalanced, rawRowCheck2122]

def rawRow2123 : Integer.Sparse Key := [(key1308, -6), (key1334, 2), (key1288, 2), (key1308, 2), (key1538, 6), (key1769, -2), (key1383, -2), (key1538, -2), (key1652, -2), (key1565, -2), (key1614, -2), (key1810, 2), (key1416, 2), (key1614, 2)]

theorem rawRowCheck2123 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form1 = rawRow2123 := by decide +kernel

def row2123 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, -2), (key1416, 2), (key1538, 4), (key1565, -2), (key1652, -2), (key1769, -2), (key1810, 2)]

theorem rowCheck2123 : row2123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2123 := by decide +kernel

theorem rowEval2123 (x : Key → ℝ) : Integer.Sparse.eval row2123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2123, Integer.Sparse.eval_collectBalanced, rawRowCheck2123]

def rawRow2124 : Integer.Sparse Key := [(key1308, -6), (key1334, 2), (key1308, 2), (key1288, 2), (key1538, 6), (key1769, -2), (key1538, -2), (key1383, -2), (key1652, -2), (key1614, -2), (key1565, -2), (key1810, 2), (key1614, 2), (key1416, 2)]

theorem rawRowCheck2124 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form1 = rawRow2124 := by decide +kernel

def row2124 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, -2), (key1416, 2), (key1538, 4), (key1565, -2), (key1652, -2), (key1769, -2), (key1810, 2)]

theorem rowCheck2124 : row2124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2124 := by decide +kernel

theorem rowEval2124 (x : Key → ℝ) : Integer.Sparse.eval row2124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2124, Integer.Sparse.eval_collectBalanced, rawRowCheck2124]

def rawRow2125 : Integer.Sparse Key := [(key1383, -6), (key1416, 2), (key1416, 2), (key1452, 2), (key1288, 6), (key1565, -2), (key1565, -2), (key1785, -2), (key1308, -2), (key1308, -2), (key1334, -2), (key1538, 2), (key1538, 2), (key1769, 2)]

theorem rawRowCheck2125 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form1 = rawRow2125 := by decide +kernel

def row2125 : Integer.Sparse Key := [(key1288, 6), (key1308, -4), (key1334, -2), (key1383, -6), (key1416, 4), (key1452, 2), (key1538, 4), (key1565, -4), (key1769, 2), (key1785, -2)]

theorem rowCheck2125 : row2125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2125 := by decide +kernel

theorem rowEval2125 (x : Key → ℝ) : Integer.Sparse.eval row2125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2125, Integer.Sparse.eval_collectBalanced, rawRowCheck2125]

def rawRow2126 : Integer.Sparse Key := [(key1383, -6), (key1416, 2), (key1452, 2), (key1416, 2), (key1288, 6), (key1565, -2), (key1785, -2), (key1565, -2), (key1308, -2), (key1334, -2), (key1308, -2), (key1538, 2), (key1769, 2), (key1538, 2)]

theorem rawRowCheck2126 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form1 = rawRow2126 := by decide +kernel

def row2126 : Integer.Sparse Key := [(key1288, 6), (key1308, -4), (key1334, -2), (key1383, -6), (key1416, 4), (key1452, 2), (key1538, 4), (key1565, -4), (key1769, 2), (key1785, -2)]

theorem rowCheck2126 : row2126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2126 := by decide +kernel

theorem rowEval2126 (x : Key → ℝ) : Integer.Sparse.eval row2126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2126, Integer.Sparse.eval_collectBalanced, rawRowCheck2126]

def rawRow2127 : Integer.Sparse Key := [(key1383, -6), (key1452, 2), (key1416, 2), (key1416, 2), (key1288, 6), (key1785, -2), (key1565, -2), (key1565, -2), (key1334, -2), (key1308, -2), (key1308, -2), (key1769, 2), (key1538, 2), (key1538, 2)]

theorem rawRowCheck2127 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form1 = rawRow2127 := by decide +kernel

def row2127 : Integer.Sparse Key := [(key1288, 6), (key1308, -4), (key1334, -2), (key1383, -6), (key1416, 4), (key1452, 2), (key1538, 4), (key1565, -4), (key1769, 2), (key1785, -2)]

theorem rowCheck2127 : row2127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2127 := by decide +kernel

theorem rowEval2127 (x : Key → ℝ) : Integer.Sparse.eval row2127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2127, Integer.Sparse.eval_collectBalanced, rawRowCheck2127]

def rawRow2128 : Integer.Sparse Key := [(key1416, -6), (key1383, 2), (key1416, 2), (key1452, 2), (key1565, 6), (key1288, -2), (key1565, -2), (key1785, -2), (key1538, -2), (key1614, -2), (key1652, -2), (key1308, 2), (key1614, 2), (key1810, 2)]

theorem rawRowCheck2128 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form1 = rawRow2128 := by decide +kernel

def row2128 : Integer.Sparse Key := [(key1288, -2), (key1308, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, -2), (key1565, 4), (key1652, -2), (key1785, -2), (key1810, 2)]

theorem rowCheck2128 : row2128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2128 := by decide +kernel

theorem rowEval2128 (x : Key → ℝ) : Integer.Sparse.eval row2128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2128, Integer.Sparse.eval_collectBalanced, rawRowCheck2128]

def rawRow2129 : Integer.Sparse Key := [(key1416, -6), (key1383, 2), (key1452, 2), (key1416, 2), (key1565, 6), (key1288, -2), (key1785, -2), (key1565, -2), (key1538, -2), (key1652, -2), (key1614, -2), (key1308, 2), (key1810, 2), (key1614, 2)]

theorem rawRowCheck2129 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form1 = rawRow2129 := by decide +kernel

def row2129 : Integer.Sparse Key := [(key1288, -2), (key1308, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, -2), (key1565, 4), (key1652, -2), (key1785, -2), (key1810, 2)]

theorem rowCheck2129 : row2129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2129 := by decide +kernel

theorem rowEval2129 (x : Key → ℝ) : Integer.Sparse.eval row2129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2129, Integer.Sparse.eval_collectBalanced, rawRowCheck2129]

def rawRow2130 : Integer.Sparse Key := [(key1416, -6), (key1416, 2), (key1383, 2), (key1452, 2), (key1565, 6), (key1565, -2), (key1288, -2), (key1785, -2), (key1614, -2), (key1538, -2), (key1652, -2), (key1614, 2), (key1308, 2), (key1810, 2)]

theorem rawRowCheck2130 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form1 = rawRow2130 := by decide +kernel

def row2130 : Integer.Sparse Key := [(key1288, -2), (key1308, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, -2), (key1565, 4), (key1652, -2), (key1785, -2), (key1810, 2)]

theorem rowCheck2130 : row2130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2130 := by decide +kernel

theorem rowEval2130 (x : Key → ℝ) : Integer.Sparse.eval row2130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2130, Integer.Sparse.eval_collectBalanced, rawRowCheck2130]

def rawRow2131 : Integer.Sparse Key := [(key1416, -6), (key1416, 2), (key1452, 2), (key1383, 2), (key1565, 6), (key1565, -2), (key1785, -2), (key1288, -2), (key1614, -2), (key1652, -2), (key1538, -2), (key1614, 2), (key1810, 2), (key1308, 2)]

theorem rawRowCheck2131 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form1 = rawRow2131 := by decide +kernel

def row2131 : Integer.Sparse Key := [(key1288, -2), (key1308, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, -2), (key1565, 4), (key1652, -2), (key1785, -2), (key1810, 2)]

theorem rowCheck2131 : row2131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2131 := by decide +kernel

theorem rowEval2131 (x : Key → ℝ) : Integer.Sparse.eval row2131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck2131, Integer.Sparse.eval_collectBalanced, rawRowCheck2131]

def rawRow2132 : Integer.Sparse Key := [(key1416, -6), (key1452, 2), (key1383, 2), (key1416, 2), (key1565, 6), (key1785, -2), (key1288, -2), (key1565, -2), (key1652, -2), (key1538, -2), (key1614, -2), (key1810, 2), (key1308, 2), (key1614, 2)]

theorem rawRowCheck2132 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form1 = rawRow2132 := by decide +kernel

def row2132 : Integer.Sparse Key := [(key1288, -2), (key1308, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, -2), (key1565, 4), (key1652, -2), (key1785, -2), (key1810, 2)]

theorem rowCheck2132 : row2132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2132 := by decide +kernel

theorem rowEval2132 (x : Key → ℝ) : Integer.Sparse.eval row2132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2132, Integer.Sparse.eval_collectBalanced, rawRowCheck2132]

def rawRow2133 : Integer.Sparse Key := [(key1416, -6), (key1452, 2), (key1416, 2), (key1383, 2), (key1565, 6), (key1785, -2), (key1565, -2), (key1288, -2), (key1652, -2), (key1614, -2), (key1538, -2), (key1810, 2), (key1614, 2), (key1308, 2)]

theorem rawRowCheck2133 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form1 = rawRow2133 := by decide +kernel

def row2133 : Integer.Sparse Key := [(key1288, -2), (key1308, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, -2), (key1565, 4), (key1652, -2), (key1785, -2), (key1810, 2)]

theorem rowCheck2133 : row2133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2133 := by decide +kernel

theorem rowEval2133 (x : Key → ℝ) : Integer.Sparse.eval row2133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck2133, Integer.Sparse.eval_collectBalanced, rawRowCheck2133]

def rawRow2134 : Integer.Sparse Key := [(key1538, -6), (key1565, 2), (key1614, 2), (key1652, 2), (key1308, 6), (key1416, -2), (key1614, -2), (key1810, -2), (key1288, -2), (key1308, -2), (key1334, -2), (key1383, 2), (key1538, 2), (key1769, 2)]

theorem rawRowCheck2134 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form1 = rawRow2134 := by decide +kernel

def row2134 : Integer.Sparse Key := [(key1288, -2), (key1308, 4), (key1334, -2), (key1383, 2), (key1416, -2), (key1538, -4), (key1565, 2), (key1652, 2), (key1769, 2), (key1810, -2)]

theorem rowCheck2134 : row2134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2134 := by decide +kernel

theorem rowEval2134 (x : Key → ℝ) : Integer.Sparse.eval row2134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2134, Integer.Sparse.eval_collectBalanced, rawRowCheck2134]

def rawRow2135 : Integer.Sparse Key := [(key1538, -6), (key1565, 2), (key1652, 2), (key1614, 2), (key1308, 6), (key1416, -2), (key1810, -2), (key1614, -2), (key1288, -2), (key1334, -2), (key1308, -2), (key1383, 2), (key1769, 2), (key1538, 2)]

theorem rawRowCheck2135 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form1 = rawRow2135 := by decide +kernel

def row2135 : Integer.Sparse Key := [(key1288, -2), (key1308, 4), (key1334, -2), (key1383, 2), (key1416, -2), (key1538, -4), (key1565, 2), (key1652, 2), (key1769, 2), (key1810, -2)]

theorem rowCheck2135 : row2135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2135 := by decide +kernel

theorem rowEval2135 (x : Key → ℝ) : Integer.Sparse.eval row2135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2135, Integer.Sparse.eval_collectBalanced, rawRowCheck2135]

def rawRow2136 : Integer.Sparse Key := [(key1538, -6), (key1614, 2), (key1565, 2), (key1652, 2), (key1308, 6), (key1614, -2), (key1416, -2), (key1810, -2), (key1308, -2), (key1288, -2), (key1334, -2), (key1538, 2), (key1383, 2), (key1769, 2)]

theorem rawRowCheck2136 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form1 = rawRow2136 := by decide +kernel

def row2136 : Integer.Sparse Key := [(key1288, -2), (key1308, 4), (key1334, -2), (key1383, 2), (key1416, -2), (key1538, -4), (key1565, 2), (key1652, 2), (key1769, 2), (key1810, -2)]

theorem rowCheck2136 : row2136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2136 := by decide +kernel

theorem rowEval2136 (x : Key → ℝ) : Integer.Sparse.eval row2136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2136, Integer.Sparse.eval_collectBalanced, rawRowCheck2136]

def rawRow2137 : Integer.Sparse Key := [(key1538, -6), (key1614, 2), (key1652, 2), (key1565, 2), (key1308, 6), (key1614, -2), (key1810, -2), (key1416, -2), (key1308, -2), (key1334, -2), (key1288, -2), (key1538, 2), (key1769, 2), (key1383, 2)]

theorem rawRowCheck2137 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form1 = rawRow2137 := by decide +kernel

def row2137 : Integer.Sparse Key := [(key1288, -2), (key1308, 4), (key1334, -2), (key1383, 2), (key1416, -2), (key1538, -4), (key1565, 2), (key1652, 2), (key1769, 2), (key1810, -2)]

theorem rowCheck2137 : row2137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2137 := by decide +kernel

theorem rowEval2137 (x : Key → ℝ) : Integer.Sparse.eval row2137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2137, Integer.Sparse.eval_collectBalanced, rawRowCheck2137]

def rawRow2138 : Integer.Sparse Key := [(key1538, -6), (key1652, 2), (key1565, 2), (key1614, 2), (key1308, 6), (key1810, -2), (key1416, -2), (key1614, -2), (key1334, -2), (key1288, -2), (key1308, -2), (key1769, 2), (key1383, 2), (key1538, 2)]

theorem rawRowCheck2138 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form1 = rawRow2138 := by decide +kernel

def row2138 : Integer.Sparse Key := [(key1288, -2), (key1308, 4), (key1334, -2), (key1383, 2), (key1416, -2), (key1538, -4), (key1565, 2), (key1652, 2), (key1769, 2), (key1810, -2)]

theorem rowCheck2138 : row2138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2138 := by decide +kernel

theorem rowEval2138 (x : Key → ℝ) : Integer.Sparse.eval row2138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2138, Integer.Sparse.eval_collectBalanced, rawRowCheck2138]

def rawRow2139 : Integer.Sparse Key := [(key1538, -6), (key1652, 2), (key1614, 2), (key1565, 2), (key1308, 6), (key1810, -2), (key1614, -2), (key1416, -2), (key1334, -2), (key1308, -2), (key1288, -2), (key1769, 2), (key1538, 2), (key1383, 2)]

theorem rawRowCheck2139 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form1 = rawRow2139 := by decide +kernel

def row2139 : Integer.Sparse Key := [(key1288, -2), (key1308, 4), (key1334, -2), (key1383, 2), (key1416, -2), (key1538, -4), (key1565, 2), (key1652, 2), (key1769, 2), (key1810, -2)]

theorem rowCheck2139 : row2139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2139 := by decide +kernel

theorem rowEval2139 (x : Key → ℝ) : Integer.Sparse.eval row2139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2139, Integer.Sparse.eval_collectBalanced, rawRowCheck2139]

def rawRow2140 : Integer.Sparse Key := [(key1565, -6), (key1538, 2), (key1614, 2), (key1652, 2), (key1416, 6), (key1308, -2), (key1614, -2), (key1810, -2), (key1383, -2), (key1416, -2), (key1452, -2), (key1288, 2), (key1565, 2), (key1785, 2)]

theorem rawRowCheck2140 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form1 = rawRow2140 := by decide +kernel

def row2140 : Integer.Sparse Key := [(key1288, 2), (key1308, -2), (key1383, -2), (key1416, 4), (key1452, -2), (key1538, 2), (key1565, -4), (key1652, 2), (key1785, 2), (key1810, -2)]

theorem rowCheck2140 : row2140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2140 := by decide +kernel

theorem rowEval2140 (x : Key → ℝ) : Integer.Sparse.eval row2140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2140, Integer.Sparse.eval_collectBalanced, rawRowCheck2140]

def rawRow2141 : Integer.Sparse Key := [(key1565, -6), (key1538, 2), (key1652, 2), (key1614, 2), (key1416, 6), (key1308, -2), (key1810, -2), (key1614, -2), (key1383, -2), (key1452, -2), (key1416, -2), (key1288, 2), (key1785, 2), (key1565, 2)]

theorem rawRowCheck2141 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form1 = rawRow2141 := by decide +kernel

def row2141 : Integer.Sparse Key := [(key1288, 2), (key1308, -2), (key1383, -2), (key1416, 4), (key1452, -2), (key1538, 2), (key1565, -4), (key1652, 2), (key1785, 2), (key1810, -2)]

theorem rowCheck2141 : row2141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2141 := by decide +kernel

theorem rowEval2141 (x : Key → ℝ) : Integer.Sparse.eval row2141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2141, Integer.Sparse.eval_collectBalanced, rawRowCheck2141]

def rawRow2142 : Integer.Sparse Key := [(key1565, -6), (key1614, 2), (key1538, 2), (key1652, 2), (key1416, 6), (key1614, -2), (key1308, -2), (key1810, -2), (key1416, -2), (key1383, -2), (key1452, -2), (key1565, 2), (key1288, 2), (key1785, 2)]

theorem rawRowCheck2142 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form1 = rawRow2142 := by decide +kernel

def row2142 : Integer.Sparse Key := [(key1288, 2), (key1308, -2), (key1383, -2), (key1416, 4), (key1452, -2), (key1538, 2), (key1565, -4), (key1652, 2), (key1785, 2), (key1810, -2)]

theorem rowCheck2142 : row2142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2142 := by decide +kernel

theorem rowEval2142 (x : Key → ℝ) : Integer.Sparse.eval row2142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form1) x := by
  rw [rowCheck2142, Integer.Sparse.eval_collectBalanced, rawRowCheck2142]

def rawRow2143 : Integer.Sparse Key := [(key1565, -6), (key1614, 2), (key1652, 2), (key1538, 2), (key1416, 6), (key1614, -2), (key1810, -2), (key1308, -2), (key1416, -2), (key1452, -2), (key1383, -2), (key1565, 2), (key1785, 2), (key1288, 2)]

theorem rawRowCheck2143 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form1 = rawRow2143 := by decide +kernel

def row2143 : Integer.Sparse Key := [(key1288, 2), (key1308, -2), (key1383, -2), (key1416, 4), (key1452, -2), (key1538, 2), (key1565, -4), (key1652, 2), (key1785, 2), (key1810, -2)]

theorem rowCheck2143 : row2143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2143 := by decide +kernel

theorem rowEval2143 (x : Key → ℝ) : Integer.Sparse.eval row2143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck2143, Integer.Sparse.eval_collectBalanced, rawRowCheck2143]

def rawRow2144 : Integer.Sparse Key := [(key1565, -6), (key1652, 2), (key1538, 2), (key1614, 2), (key1416, 6), (key1810, -2), (key1308, -2), (key1614, -2), (key1452, -2), (key1383, -2), (key1416, -2), (key1785, 2), (key1288, 2), (key1565, 2)]

theorem rawRowCheck2144 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form1 = rawRow2144 := by decide +kernel

def row2144 : Integer.Sparse Key := [(key1288, 2), (key1308, -2), (key1383, -2), (key1416, 4), (key1452, -2), (key1538, 2), (key1565, -4), (key1652, 2), (key1785, 2), (key1810, -2)]

theorem rowCheck2144 : row2144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2144 := by decide +kernel

theorem rowEval2144 (x : Key → ℝ) : Integer.Sparse.eval row2144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form1) x := by
  rw [rowCheck2144, Integer.Sparse.eval_collectBalanced, rawRowCheck2144]

def rawRow2145 : Integer.Sparse Key := [(key1565, -6), (key1652, 2), (key1614, 2), (key1538, 2), (key1416, 6), (key1810, -2), (key1614, -2), (key1308, -2), (key1452, -2), (key1416, -2), (key1383, -2), (key1785, 2), (key1565, 2), (key1288, 2)]

theorem rawRowCheck2145 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form1 = rawRow2145 := by decide +kernel

def row2145 : Integer.Sparse Key := [(key1288, 2), (key1308, -2), (key1383, -2), (key1416, 4), (key1452, -2), (key1538, 2), (key1565, -4), (key1652, 2), (key1785, 2), (key1810, -2)]

theorem rowCheck2145 : row2145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2145 := by decide +kernel

theorem rowEval2145 (x : Key → ℝ) : Integer.Sparse.eval row2145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form1) x := by
  rw [rowCheck2145, Integer.Sparse.eval_collectBalanced, rawRowCheck2145]

def rawRow2146 : Integer.Sparse Key := [(key2609, -2), (key2613, -2), (key2613, -2), (key2625, 1), (key2629, 1), (key2625, 1), (key2647, 1), (key2629, 1), (key2647, 1), (key2664, 2), (key2668, 2), (key2668, 2), (key2779, -1), (key2783, -1), (key2779, -1), (key2937, -1), (key2783, -1), (key2937, -1), (key2699, -1), (key2703, -1), (key2699, -1), (key2736, -1), (key2703, -1), (key2736, -1), (key2802, 1), (key2806, 1), (key2802, 1), (key2949, 1), (key2806, 1), (key2949, 1)]

theorem rawRowCheck2146 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form2 = rawRow2146 := by decide +kernel

def row2146 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2664, 2), (key2668, 4), (key2699, -2), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, -2), (key2802, 2), (key2806, 2), (key2937, -2), (key2949, 2)]

theorem rowCheck2146 : row2146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2146 := by decide +kernel

theorem rowEval2146 (x : Key → ℝ) : Integer.Sparse.eval row2146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2146, Integer.Sparse.eval_collectBalanced, rawRowCheck2146]

def rawRow2147 : Integer.Sparse Key := [(key2613, -2), (key2609, -2), (key2613, -2), (key2629, 1), (key2625, 1), (key2647, 1), (key2625, 1), (key2647, 1), (key2629, 1), (key2668, 2), (key2664, 2), (key2668, 2), (key2783, -1), (key2779, -1), (key2937, -1), (key2779, -1), (key2937, -1), (key2783, -1), (key2703, -1), (key2699, -1), (key2736, -1), (key2699, -1), (key2736, -1), (key2703, -1), (key2806, 1), (key2802, 1), (key2949, 1), (key2802, 1), (key2949, 1), (key2806, 1)]

theorem rawRowCheck2147 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form2 = rawRow2147 := by decide +kernel

def row2147 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2664, 2), (key2668, 4), (key2699, -2), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, -2), (key2802, 2), (key2806, 2), (key2937, -2), (key2949, 2)]

theorem rowCheck2147 : row2147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2147 := by decide +kernel

theorem rowEval2147 (x : Key → ℝ) : Integer.Sparse.eval row2147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 0, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2147, Integer.Sparse.eval_collectBalanced, rawRowCheck2147]

def rawRow2148 : Integer.Sparse Key := [(key2613, -2), (key2613, -2), (key2609, -2), (key2647, 1), (key2647, 1), (key2629, 1), (key2629, 1), (key2625, 1), (key2625, 1), (key2668, 2), (key2668, 2), (key2664, 2), (key2937, -1), (key2937, -1), (key2783, -1), (key2783, -1), (key2779, -1), (key2779, -1), (key2736, -1), (key2736, -1), (key2703, -1), (key2703, -1), (key2699, -1), (key2699, -1), (key2949, 1), (key2949, 1), (key2806, 1), (key2806, 1), (key2802, 1), (key2802, 1)]

theorem rawRowCheck2148 : GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form2 = rawRow2148 := by decide +kernel

def row2148 : Integer.Sparse Key := [(key2609, -2), (key2613, -4), (key2625, 2), (key2629, 2), (key2647, 2), (key2664, 2), (key2668, 4), (key2699, -2), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, -2), (key2802, 2), (key2806, 2), (key2937, -2), (key2949, 2)]

theorem rowCheck2148 : row2148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2148 := by decide +kernel

theorem rowEval2148 (x : Key → ℝ) : Integer.Sparse.eval row2148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, -1, 1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2148, Integer.Sparse.eval_collectBalanced, rawRowCheck2148]

def rawRow2149 : Integer.Sparse Key := [(key2625, -2), (key2629, -2), (key2637, -2), (key2609, 1), (key2613, 1), (key2625, 1), (key2647, 1), (key2637, 1), (key2652, 1), (key2779, 2), (key2783, 2), (key2791, 2), (key2664, -1), (key2668, -1), (key2779, -1), (key2937, -1), (key2791, -1), (key2942, -1), (key2802, -1), (key2806, -1), (key2852, -1), (key2894, -1), (key2857, -1), (key2896, -1), (key2699, 1), (key2703, 1), (key2852, 1), (key2973, 1), (key2857, 1), (key2975, 1)]

theorem rawRowCheck2149 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form2 = rawRow2149 := by decide +kernel

def row2149 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, -1), (key2806, -1), (key2894, -1), (key2896, -1), (key2937, -1), (key2942, -1), (key2973, 1), (key2975, 1)]

theorem rowCheck2149 : row2149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2149 := by decide +kernel

theorem rowEval2149 (x : Key → ℝ) : Integer.Sparse.eval row2149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2149, Integer.Sparse.eval_collectBalanced, rawRowCheck2149]

def rawRow2150 : Integer.Sparse Key := [(key2629, -2), (key2625, -2), (key2637, -2), (key2613, 1), (key2609, 1), (key2647, 1), (key2625, 1), (key2652, 1), (key2637, 1), (key2783, 2), (key2779, 2), (key2791, 2), (key2668, -1), (key2664, -1), (key2937, -1), (key2779, -1), (key2942, -1), (key2791, -1), (key2806, -1), (key2802, -1), (key2894, -1), (key2852, -1), (key2896, -1), (key2857, -1), (key2703, 1), (key2699, 1), (key2973, 1), (key2852, 1), (key2975, 1), (key2857, 1)]

theorem rawRowCheck2150 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form2 = rawRow2150 := by decide +kernel

def row2150 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, -1), (key2806, -1), (key2894, -1), (key2896, -1), (key2937, -1), (key2942, -1), (key2973, 1), (key2975, 1)]

theorem rowCheck2150 : row2150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2150 := by decide +kernel

theorem rowEval2150 (x : Key → ℝ) : Integer.Sparse.eval row2150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2150, Integer.Sparse.eval_collectBalanced, rawRowCheck2150]

def rawRow2151 : Integer.Sparse Key := [(key2625, -2), (key2637, -2), (key2629, -2), (key2625, 1), (key2637, 1), (key2609, 1), (key2652, 1), (key2613, 1), (key2647, 1), (key2779, 2), (key2791, 2), (key2783, 2), (key2779, -1), (key2791, -1), (key2664, -1), (key2942, -1), (key2668, -1), (key2937, -1), (key2852, -1), (key2857, -1), (key2802, -1), (key2896, -1), (key2806, -1), (key2894, -1), (key2852, 1), (key2857, 1), (key2699, 1), (key2975, 1), (key2703, 1), (key2973, 1)]

theorem rawRowCheck2151 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form2 = rawRow2151 := by decide +kernel

def row2151 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, -1), (key2806, -1), (key2894, -1), (key2896, -1), (key2937, -1), (key2942, -1), (key2973, 1), (key2975, 1)]

theorem rowCheck2151 : row2151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2151 := by decide +kernel

theorem rowEval2151 (x : Key → ℝ) : Integer.Sparse.eval row2151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2151, Integer.Sparse.eval_collectBalanced, rawRowCheck2151]

def rawRow2152 : Integer.Sparse Key := [(key2637, -2), (key2625, -2), (key2629, -2), (key2637, 1), (key2625, 1), (key2652, 1), (key2609, 1), (key2647, 1), (key2613, 1), (key2791, 2), (key2779, 2), (key2783, 2), (key2791, -1), (key2779, -1), (key2942, -1), (key2664, -1), (key2937, -1), (key2668, -1), (key2857, -1), (key2852, -1), (key2896, -1), (key2802, -1), (key2894, -1), (key2806, -1), (key2857, 1), (key2852, 1), (key2975, 1), (key2699, 1), (key2973, 1), (key2703, 1)]

theorem rawRowCheck2152 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form2 = rawRow2152 := by decide +kernel

def row2152 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, -1), (key2806, -1), (key2894, -1), (key2896, -1), (key2937, -1), (key2942, -1), (key2973, 1), (key2975, 1)]

theorem rowCheck2152 : row2152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2152 := by decide +kernel

theorem rowEval2152 (x : Key → ℝ) : Integer.Sparse.eval row2152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2152, Integer.Sparse.eval_collectBalanced, rawRowCheck2152]

def rawRow2153 : Integer.Sparse Key := [(key2629, -2), (key2637, -2), (key2625, -2), (key2647, 1), (key2652, 1), (key2613, 1), (key2637, 1), (key2609, 1), (key2625, 1), (key2783, 2), (key2791, 2), (key2779, 2), (key2937, -1), (key2942, -1), (key2668, -1), (key2791, -1), (key2664, -1), (key2779, -1), (key2894, -1), (key2896, -1), (key2806, -1), (key2857, -1), (key2802, -1), (key2852, -1), (key2973, 1), (key2975, 1), (key2703, 1), (key2857, 1), (key2699, 1), (key2852, 1)]

theorem rawRowCheck2153 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form2 = rawRow2153 := by decide +kernel

def row2153 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, -1), (key2806, -1), (key2894, -1), (key2896, -1), (key2937, -1), (key2942, -1), (key2973, 1), (key2975, 1)]

theorem rowCheck2153 : row2153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2153 := by decide +kernel

theorem rowEval2153 (x : Key → ℝ) : Integer.Sparse.eval row2153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2153, Integer.Sparse.eval_collectBalanced, rawRowCheck2153]

def rawRow2154 : Integer.Sparse Key := [(key2637, -2), (key2629, -2), (key2625, -2), (key2652, 1), (key2647, 1), (key2637, 1), (key2613, 1), (key2625, 1), (key2609, 1), (key2791, 2), (key2783, 2), (key2779, 2), (key2942, -1), (key2937, -1), (key2791, -1), (key2668, -1), (key2779, -1), (key2664, -1), (key2896, -1), (key2894, -1), (key2857, -1), (key2806, -1), (key2852, -1), (key2802, -1), (key2975, 1), (key2973, 1), (key2857, 1), (key2703, 1), (key2852, 1), (key2699, 1)]

theorem rawRowCheck2154 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form2 = rawRow2154 := by decide +kernel

def row2154 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -2), (key2637, -1), (key2647, 1), (key2652, 1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 1), (key2779, 1), (key2783, 2), (key2791, 1), (key2802, -1), (key2806, -1), (key2894, -1), (key2896, -1), (key2937, -1), (key2942, -1), (key2973, 1), (key2975, 1)]

theorem rowCheck2154 : row2154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2154 := by decide +kernel

theorem rowEval2154 (x : Key → ℝ) : Integer.Sparse.eval row2154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2154, Integer.Sparse.eval_collectBalanced, rawRowCheck2154]

def rawRow2155 : Integer.Sparse Key := [(key2664, -2), (key2668, -2), (key2668, -2), (key2699, 1), (key2703, 1), (key2699, 1), (key2736, 1), (key2703, 1), (key2736, 1), (key2609, 2), (key2613, 2), (key2613, 2), (key2802, -1), (key2806, -1), (key2802, -1), (key2949, -1), (key2806, -1), (key2949, -1), (key2625, -1), (key2629, -1), (key2625, -1), (key2647, -1), (key2629, -1), (key2647, -1), (key2779, 1), (key2783, 1), (key2779, 1), (key2937, 1), (key2783, 1), (key2937, 1)]

theorem rawRowCheck2155 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form2 = rawRow2155 := by decide +kernel

def row2155 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2625, -2), (key2629, -2), (key2647, -2), (key2664, -2), (key2668, -4), (key2699, 2), (key2703, 2), (key2736, 2), (key2779, 2), (key2783, 2), (key2802, -2), (key2806, -2), (key2937, 2), (key2949, -2)]

theorem rowCheck2155 : row2155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2155 := by decide +kernel

theorem rowEval2155 (x : Key → ℝ) : Integer.Sparse.eval row2155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2155, Integer.Sparse.eval_collectBalanced, rawRowCheck2155]

def rawRow2156 : Integer.Sparse Key := [(key2668, -2), (key2664, -2), (key2668, -2), (key2703, 1), (key2699, 1), (key2736, 1), (key2699, 1), (key2736, 1), (key2703, 1), (key2613, 2), (key2609, 2), (key2613, 2), (key2806, -1), (key2802, -1), (key2949, -1), (key2802, -1), (key2949, -1), (key2806, -1), (key2629, -1), (key2625, -1), (key2647, -1), (key2625, -1), (key2647, -1), (key2629, -1), (key2783, 1), (key2779, 1), (key2937, 1), (key2779, 1), (key2937, 1), (key2783, 1)]

theorem rawRowCheck2156 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form2 = rawRow2156 := by decide +kernel

def row2156 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2625, -2), (key2629, -2), (key2647, -2), (key2664, -2), (key2668, -4), (key2699, 2), (key2703, 2), (key2736, 2), (key2779, 2), (key2783, 2), (key2802, -2), (key2806, -2), (key2937, 2), (key2949, -2)]

theorem rowCheck2156 : row2156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2156 := by decide +kernel

theorem rowEval2156 (x : Key → ℝ) : Integer.Sparse.eval row2156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 0, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2156, Integer.Sparse.eval_collectBalanced, rawRowCheck2156]

def rawRow2157 : Integer.Sparse Key := [(key2668, -2), (key2668, -2), (key2664, -2), (key2736, 1), (key2736, 1), (key2703, 1), (key2703, 1), (key2699, 1), (key2699, 1), (key2613, 2), (key2613, 2), (key2609, 2), (key2949, -1), (key2949, -1), (key2806, -1), (key2806, -1), (key2802, -1), (key2802, -1), (key2647, -1), (key2647, -1), (key2629, -1), (key2629, -1), (key2625, -1), (key2625, -1), (key2937, 1), (key2937, 1), (key2783, 1), (key2783, 1), (key2779, 1), (key2779, 1)]

theorem rawRowCheck2157 : GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form2 = rawRow2157 := by decide +kernel

def row2157 : Integer.Sparse Key := [(key2609, 2), (key2613, 4), (key2625, -2), (key2629, -2), (key2647, -2), (key2664, -2), (key2668, -4), (key2699, 2), (key2703, 2), (key2736, 2), (key2779, 2), (key2783, 2), (key2802, -2), (key2806, -2), (key2937, 2), (key2949, -2)]

theorem rowCheck2157 : row2157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2157 := by decide +kernel

theorem rowEval2157 (x : Key → ℝ) : Integer.Sparse.eval row2157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -2, 1, 0, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2157, Integer.Sparse.eval_collectBalanced, rawRowCheck2157]

def rawRow2158 : Integer.Sparse Key := [(key2699, -2), (key2703, -2), (key2723, -2), (key2664, 1), (key2668, 1), (key2699, 1), (key2736, 1), (key2723, 1), (key2746, 1), (key2802, 2), (key2806, 2), (key2826, 2), (key2609, -1), (key2613, -1), (key2802, -1), (key2949, -1), (key2826, -1), (key2959, -1), (key2779, -1), (key2783, -1), (key2852, -1), (key2894, -1), (key2867, -1), (key2903, -1), (key2625, 1), (key2629, 1), (key2852, 1), (key2973, 1), (key2867, 1), (key2982, 1)]

theorem rawRowCheck2158 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form2 = rawRow2158 := by decide +kernel

def row2158 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, -1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2894, -1), (key2903, -1), (key2949, -1), (key2959, -1), (key2973, 1), (key2982, 1)]

theorem rowCheck2158 : row2158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2158 := by decide +kernel

theorem rowEval2158 (x : Key → ℝ) : Integer.Sparse.eval row2158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2158, Integer.Sparse.eval_collectBalanced, rawRowCheck2158]

def rawRow2159 : Integer.Sparse Key := [(key2703, -2), (key2699, -2), (key2723, -2), (key2668, 1), (key2664, 1), (key2736, 1), (key2699, 1), (key2746, 1), (key2723, 1), (key2806, 2), (key2802, 2), (key2826, 2), (key2613, -1), (key2609, -1), (key2949, -1), (key2802, -1), (key2959, -1), (key2826, -1), (key2783, -1), (key2779, -1), (key2894, -1), (key2852, -1), (key2903, -1), (key2867, -1), (key2629, 1), (key2625, 1), (key2973, 1), (key2852, 1), (key2982, 1), (key2867, 1)]

theorem rawRowCheck2159 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form2 = rawRow2159 := by decide +kernel

def row2159 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, -1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2894, -1), (key2903, -1), (key2949, -1), (key2959, -1), (key2973, 1), (key2982, 1)]

theorem rowCheck2159 : row2159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2159 := by decide +kernel

theorem rowEval2159 (x : Key → ℝ) : Integer.Sparse.eval row2159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -2, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2159, Integer.Sparse.eval_collectBalanced, rawRowCheck2159]

def rawRow2160 : Integer.Sparse Key := [(key2699, -2), (key2723, -2), (key2703, -2), (key2699, 1), (key2723, 1), (key2664, 1), (key2746, 1), (key2668, 1), (key2736, 1), (key2802, 2), (key2826, 2), (key2806, 2), (key2802, -1), (key2826, -1), (key2609, -1), (key2959, -1), (key2613, -1), (key2949, -1), (key2852, -1), (key2867, -1), (key2779, -1), (key2903, -1), (key2783, -1), (key2894, -1), (key2852, 1), (key2867, 1), (key2625, 1), (key2982, 1), (key2629, 1), (key2973, 1)]

theorem rawRowCheck2160 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form2 = rawRow2160 := by decide +kernel

def row2160 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, -1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2894, -1), (key2903, -1), (key2949, -1), (key2959, -1), (key2973, 1), (key2982, 1)]

theorem rowCheck2160 : row2160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2160 := by decide +kernel

theorem rowEval2160 (x : Key → ℝ) : Integer.Sparse.eval row2160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, -2, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2160, Integer.Sparse.eval_collectBalanced, rawRowCheck2160]

def rawRow2161 : Integer.Sparse Key := [(key2723, -2), (key2699, -2), (key2703, -2), (key2723, 1), (key2699, 1), (key2746, 1), (key2664, 1), (key2736, 1), (key2668, 1), (key2826, 2), (key2802, 2), (key2806, 2), (key2826, -1), (key2802, -1), (key2959, -1), (key2609, -1), (key2949, -1), (key2613, -1), (key2867, -1), (key2852, -1), (key2903, -1), (key2779, -1), (key2894, -1), (key2783, -1), (key2867, 1), (key2852, 1), (key2982, 1), (key2625, 1), (key2973, 1), (key2629, 1)]

theorem rawRowCheck2161 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form2 = rawRow2161 := by decide +kernel

def row2161 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, -1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2894, -1), (key2903, -1), (key2949, -1), (key2959, -1), (key2973, 1), (key2982, 1)]

theorem rowCheck2161 : row2161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2161 := by decide +kernel

theorem rowEval2161 (x : Key → ℝ) : Integer.Sparse.eval row2161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 0, 1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck2161, Integer.Sparse.eval_collectBalanced, rawRowCheck2161]

def rawRow2162 : Integer.Sparse Key := [(key2703, -2), (key2723, -2), (key2699, -2), (key2736, 1), (key2746, 1), (key2668, 1), (key2723, 1), (key2664, 1), (key2699, 1), (key2806, 2), (key2826, 2), (key2802, 2), (key2949, -1), (key2959, -1), (key2613, -1), (key2826, -1), (key2609, -1), (key2802, -1), (key2894, -1), (key2903, -1), (key2783, -1), (key2867, -1), (key2779, -1), (key2852, -1), (key2973, 1), (key2982, 1), (key2629, 1), (key2867, 1), (key2625, 1), (key2852, 1)]

theorem rawRowCheck2162 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form2 = rawRow2162 := by decide +kernel

def row2162 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, -1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2894, -1), (key2903, -1), (key2949, -1), (key2959, -1), (key2973, 1), (key2982, 1)]

theorem rowCheck2162 : row2162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2162 := by decide +kernel

theorem rowEval2162 (x : Key → ℝ) : Integer.Sparse.eval row2162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2162, Integer.Sparse.eval_collectBalanced, rawRowCheck2162]

def rawRow2163 : Integer.Sparse Key := [(key2723, -2), (key2703, -2), (key2699, -2), (key2746, 1), (key2736, 1), (key2723, 1), (key2668, 1), (key2699, 1), (key2664, 1), (key2826, 2), (key2806, 2), (key2802, 2), (key2959, -1), (key2949, -1), (key2826, -1), (key2613, -1), (key2802, -1), (key2609, -1), (key2903, -1), (key2894, -1), (key2867, -1), (key2783, -1), (key2852, -1), (key2779, -1), (key2982, 1), (key2973, 1), (key2867, 1), (key2629, 1), (key2852, 1), (key2625, 1)]

theorem rawRowCheck2163 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form2 = rawRow2163 := by decide +kernel

def row2163 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -2), (key2723, -1), (key2736, 1), (key2746, 1), (key2779, -1), (key2783, -1), (key2802, 1), (key2806, 2), (key2826, 1), (key2894, -1), (key2903, -1), (key2949, -1), (key2959, -1), (key2973, 1), (key2982, 1)]

theorem rowCheck2163 : row2163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2163 := by decide +kernel

theorem rowEval2163 (x : Key → ℝ) : Integer.Sparse.eval row2163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck2163, Integer.Sparse.eval_collectBalanced, rawRowCheck2163]

def rawRow2164 : Integer.Sparse Key := [(key2779, -2), (key2783, -2), (key2791, -2), (key2802, 1), (key2806, 1), (key2852, 1), (key2894, 1), (key2857, 1), (key2896, 1), (key2625, 2), (key2629, 2), (key2637, 2), (key2699, -1), (key2703, -1), (key2852, -1), (key2973, -1), (key2857, -1), (key2975, -1), (key2609, -1), (key2613, -1), (key2625, -1), (key2647, -1), (key2637, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2779, 1), (key2937, 1), (key2791, 1), (key2942, 1)]

theorem rawRowCheck2164 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form2 = rawRow2164 := by decide +kernel

def row2164 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, -1), (key2802, 1), (key2806, 1), (key2894, 1), (key2896, 1), (key2937, 1), (key2942, 1), (key2973, -1), (key2975, -1)]

theorem rowCheck2164 : row2164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2164 := by decide +kernel

theorem rowEval2164 (x : Key → ℝ) : Integer.Sparse.eval row2164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2164, Integer.Sparse.eval_collectBalanced, rawRowCheck2164]

def rawRow2165 : Integer.Sparse Key := [(key2783, -2), (key2779, -2), (key2791, -2), (key2806, 1), (key2802, 1), (key2894, 1), (key2852, 1), (key2896, 1), (key2857, 1), (key2629, 2), (key2625, 2), (key2637, 2), (key2703, -1), (key2699, -1), (key2973, -1), (key2852, -1), (key2975, -1), (key2857, -1), (key2613, -1), (key2609, -1), (key2647, -1), (key2625, -1), (key2652, -1), (key2637, -1), (key2668, 1), (key2664, 1), (key2937, 1), (key2779, 1), (key2942, 1), (key2791, 1)]

theorem rawRowCheck2165 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form2 = rawRow2165 := by decide +kernel

def row2165 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, -1), (key2802, 1), (key2806, 1), (key2894, 1), (key2896, 1), (key2937, 1), (key2942, 1), (key2973, -1), (key2975, -1)]

theorem rowCheck2165 : row2165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2165 := by decide +kernel

theorem rowEval2165 (x : Key → ℝ) : Integer.Sparse.eval row2165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2165, Integer.Sparse.eval_collectBalanced, rawRowCheck2165]

def rawRow2166 : Integer.Sparse Key := [(key2779, -2), (key2791, -2), (key2783, -2), (key2852, 1), (key2857, 1), (key2802, 1), (key2896, 1), (key2806, 1), (key2894, 1), (key2625, 2), (key2637, 2), (key2629, 2), (key2852, -1), (key2857, -1), (key2699, -1), (key2975, -1), (key2703, -1), (key2973, -1), (key2625, -1), (key2637, -1), (key2609, -1), (key2652, -1), (key2613, -1), (key2647, -1), (key2779, 1), (key2791, 1), (key2664, 1), (key2942, 1), (key2668, 1), (key2937, 1)]

theorem rawRowCheck2166 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form2 = rawRow2166 := by decide +kernel

def row2166 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, -1), (key2802, 1), (key2806, 1), (key2894, 1), (key2896, 1), (key2937, 1), (key2942, 1), (key2973, -1), (key2975, -1)]

theorem rowCheck2166 : row2166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2166 := by decide +kernel

theorem rowEval2166 (x : Key → ℝ) : Integer.Sparse.eval row2166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2166, Integer.Sparse.eval_collectBalanced, rawRowCheck2166]

def rawRow2167 : Integer.Sparse Key := [(key2791, -2), (key2779, -2), (key2783, -2), (key2857, 1), (key2852, 1), (key2896, 1), (key2802, 1), (key2894, 1), (key2806, 1), (key2637, 2), (key2625, 2), (key2629, 2), (key2857, -1), (key2852, -1), (key2975, -1), (key2699, -1), (key2973, -1), (key2703, -1), (key2637, -1), (key2625, -1), (key2652, -1), (key2609, -1), (key2647, -1), (key2613, -1), (key2791, 1), (key2779, 1), (key2942, 1), (key2664, 1), (key2937, 1), (key2668, 1)]

theorem rawRowCheck2167 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form2 = rawRow2167 := by decide +kernel

def row2167 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, -1), (key2802, 1), (key2806, 1), (key2894, 1), (key2896, 1), (key2937, 1), (key2942, 1), (key2973, -1), (key2975, -1)]

theorem rowCheck2167 : row2167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2167 := by decide +kernel

theorem rowEval2167 (x : Key → ℝ) : Integer.Sparse.eval row2167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2167, Integer.Sparse.eval_collectBalanced, rawRowCheck2167]

def rawRow2168 : Integer.Sparse Key := [(key2783, -2), (key2791, -2), (key2779, -2), (key2894, 1), (key2896, 1), (key2806, 1), (key2857, 1), (key2802, 1), (key2852, 1), (key2629, 2), (key2637, 2), (key2625, 2), (key2973, -1), (key2975, -1), (key2703, -1), (key2857, -1), (key2699, -1), (key2852, -1), (key2647, -1), (key2652, -1), (key2613, -1), (key2637, -1), (key2609, -1), (key2625, -1), (key2937, 1), (key2942, 1), (key2668, 1), (key2791, 1), (key2664, 1), (key2779, 1)]

theorem rawRowCheck2168 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form2 = rawRow2168 := by decide +kernel

def row2168 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, -1), (key2802, 1), (key2806, 1), (key2894, 1), (key2896, 1), (key2937, 1), (key2942, 1), (key2973, -1), (key2975, -1)]

theorem rowCheck2168 : row2168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2168 := by decide +kernel

theorem rowEval2168 (x : Key → ℝ) : Integer.Sparse.eval row2168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2168, Integer.Sparse.eval_collectBalanced, rawRowCheck2168]

def rawRow2169 : Integer.Sparse Key := [(key2791, -2), (key2783, -2), (key2779, -2), (key2896, 1), (key2894, 1), (key2857, 1), (key2806, 1), (key2852, 1), (key2802, 1), (key2637, 2), (key2629, 2), (key2625, 2), (key2975, -1), (key2973, -1), (key2857, -1), (key2703, -1), (key2852, -1), (key2699, -1), (key2652, -1), (key2647, -1), (key2637, -1), (key2613, -1), (key2625, -1), (key2609, -1), (key2942, 1), (key2937, 1), (key2791, 1), (key2668, 1), (key2779, 1), (key2664, 1)]

theorem rawRowCheck2169 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form2 = rawRow2169 := by decide +kernel

def row2169 : Integer.Sparse Key := [(key2609, -1), (key2613, -1), (key2625, 1), (key2629, 2), (key2637, 1), (key2647, -1), (key2652, -1), (key2664, 1), (key2668, 1), (key2699, -1), (key2703, -1), (key2779, -1), (key2783, -2), (key2791, -1), (key2802, 1), (key2806, 1), (key2894, 1), (key2896, 1), (key2937, 1), (key2942, 1), (key2973, -1), (key2975, -1)]

theorem rowCheck2169 : row2169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2169 := by decide +kernel

theorem rowEval2169 (x : Key → ℝ) : Integer.Sparse.eval row2169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2169, Integer.Sparse.eval_collectBalanced, rawRowCheck2169]

def rawRow2170 : Integer.Sparse Key := [(key2802, -2), (key2806, -2), (key2826, -2), (key2779, 1), (key2783, 1), (key2852, 1), (key2894, 1), (key2867, 1), (key2903, 1), (key2699, 2), (key2703, 2), (key2723, 2), (key2625, -1), (key2629, -1), (key2852, -1), (key2973, -1), (key2867, -1), (key2982, -1), (key2664, -1), (key2668, -1), (key2699, -1), (key2736, -1), (key2723, -1), (key2746, -1), (key2609, 1), (key2613, 1), (key2802, 1), (key2949, 1), (key2826, 1), (key2959, 1)]

theorem rawRowCheck2170 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form2 = rawRow2170 := by decide +kernel

def row2170 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, 1), (key2802, -1), (key2806, -2), (key2826, -1), (key2894, 1), (key2903, 1), (key2949, 1), (key2959, 1), (key2973, -1), (key2982, -1)]

theorem rowCheck2170 : row2170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2170 := by decide +kernel

theorem rowEval2170 (x : Key → ℝ) : Integer.Sparse.eval row2170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2170, Integer.Sparse.eval_collectBalanced, rawRowCheck2170]

def rawRow2171 : Integer.Sparse Key := [(key2806, -2), (key2802, -2), (key2826, -2), (key2783, 1), (key2779, 1), (key2894, 1), (key2852, 1), (key2903, 1), (key2867, 1), (key2703, 2), (key2699, 2), (key2723, 2), (key2629, -1), (key2625, -1), (key2973, -1), (key2852, -1), (key2982, -1), (key2867, -1), (key2668, -1), (key2664, -1), (key2736, -1), (key2699, -1), (key2746, -1), (key2723, -1), (key2613, 1), (key2609, 1), (key2949, 1), (key2802, 1), (key2959, 1), (key2826, 1)]

theorem rawRowCheck2171 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form2 = rawRow2171 := by decide +kernel

def row2171 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, 1), (key2802, -1), (key2806, -2), (key2826, -1), (key2894, 1), (key2903, 1), (key2949, 1), (key2959, 1), (key2973, -1), (key2982, -1)]

theorem rowCheck2171 : row2171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2171 := by decide +kernel

theorem rowEval2171 (x : Key → ℝ) : Integer.Sparse.eval row2171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2171, Integer.Sparse.eval_collectBalanced, rawRowCheck2171]

def rawRow2172 : Integer.Sparse Key := [(key2802, -2), (key2826, -2), (key2806, -2), (key2852, 1), (key2867, 1), (key2779, 1), (key2903, 1), (key2783, 1), (key2894, 1), (key2699, 2), (key2723, 2), (key2703, 2), (key2852, -1), (key2867, -1), (key2625, -1), (key2982, -1), (key2629, -1), (key2973, -1), (key2699, -1), (key2723, -1), (key2664, -1), (key2746, -1), (key2668, -1), (key2736, -1), (key2802, 1), (key2826, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2949, 1)]

theorem rawRowCheck2172 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form2 = rawRow2172 := by decide +kernel

def row2172 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, 1), (key2802, -1), (key2806, -2), (key2826, -1), (key2894, 1), (key2903, 1), (key2949, 1), (key2959, 1), (key2973, -1), (key2982, -1)]

theorem rowCheck2172 : row2172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2172 := by decide +kernel

theorem rowEval2172 (x : Key → ℝ) : Integer.Sparse.eval row2172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block1.form2) x := by
  rw [rowCheck2172, Integer.Sparse.eval_collectBalanced, rawRowCheck2172]

def rawRow2173 : Integer.Sparse Key := [(key2826, -2), (key2802, -2), (key2806, -2), (key2867, 1), (key2852, 1), (key2903, 1), (key2779, 1), (key2894, 1), (key2783, 1), (key2723, 2), (key2699, 2), (key2703, 2), (key2867, -1), (key2852, -1), (key2982, -1), (key2625, -1), (key2973, -1), (key2629, -1), (key2723, -1), (key2699, -1), (key2746, -1), (key2664, -1), (key2736, -1), (key2668, -1), (key2826, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2949, 1), (key2613, 1)]

theorem rawRowCheck2173 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form2 = rawRow2173 := by decide +kernel

def row2173 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, 1), (key2802, -1), (key2806, -2), (key2826, -1), (key2894, 1), (key2903, 1), (key2949, 1), (key2959, 1), (key2973, -1), (key2982, -1)]

theorem rowCheck2173 : row2173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2173 := by decide +kernel

theorem rowEval2173 (x : Key → ℝ) : Integer.Sparse.eval row2173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck2173, Integer.Sparse.eval_collectBalanced, rawRowCheck2173]

def rawRow2174 : Integer.Sparse Key := [(key2806, -2), (key2826, -2), (key2802, -2), (key2894, 1), (key2903, 1), (key2783, 1), (key2867, 1), (key2779, 1), (key2852, 1), (key2703, 2), (key2723, 2), (key2699, 2), (key2973, -1), (key2982, -1), (key2629, -1), (key2867, -1), (key2625, -1), (key2852, -1), (key2736, -1), (key2746, -1), (key2668, -1), (key2723, -1), (key2664, -1), (key2699, -1), (key2949, 1), (key2959, 1), (key2613, 1), (key2826, 1), (key2609, 1), (key2802, 1)]

theorem rawRowCheck2174 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form2 = rawRow2174 := by decide +kernel

def row2174 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, 1), (key2802, -1), (key2806, -2), (key2826, -1), (key2894, 1), (key2903, 1), (key2949, 1), (key2959, 1), (key2973, -1), (key2982, -1)]

theorem rowCheck2174 : row2174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2174 := by decide +kernel

theorem rowEval2174 (x : Key → ℝ) : Integer.Sparse.eval row2174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block1.form2) x := by
  rw [rowCheck2174, Integer.Sparse.eval_collectBalanced, rawRowCheck2174]

def rawRow2175 : Integer.Sparse Key := [(key2826, -2), (key2806, -2), (key2802, -2), (key2903, 1), (key2894, 1), (key2867, 1), (key2783, 1), (key2852, 1), (key2779, 1), (key2723, 2), (key2703, 2), (key2699, 2), (key2982, -1), (key2973, -1), (key2867, -1), (key2629, -1), (key2852, -1), (key2625, -1), (key2746, -1), (key2736, -1), (key2723, -1), (key2668, -1), (key2699, -1), (key2664, -1), (key2959, 1), (key2949, 1), (key2826, 1), (key2613, 1), (key2802, 1), (key2609, 1)]

theorem rawRowCheck2175 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form2 = rawRow2175 := by decide +kernel

def row2175 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, -1), (key2629, -1), (key2664, -1), (key2668, -1), (key2699, 1), (key2703, 2), (key2723, 1), (key2736, -1), (key2746, -1), (key2779, 1), (key2783, 1), (key2802, -1), (key2806, -2), (key2826, -1), (key2894, 1), (key2903, 1), (key2949, 1), (key2959, 1), (key2973, -1), (key2982, -1)]

theorem rowCheck2175 : row2175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow2175 := by decide +kernel

theorem rowEval2175 (x : Key → ℝ) : Integer.Sparse.eval row2175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block1.form2) x := by
  rw [rowCheck2175, Integer.Sparse.eval_collectBalanced, rawRowCheck2175]

end MUB6.Certificate.GramRows

end OAI
