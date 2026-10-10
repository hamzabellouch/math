import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17280 : Integer.Sparse Key := [(key1983, 2), (key1983, 2), (key1997, 2), (key1976, -2), (key1981, -2), (key1981, -2), (key2224, 2), (key2224, 2), (key2266, 2), (key1976, -1), (key1981, -1), (key1976, -1), (key2218, -1), (key1981, -1), (key2218, -1), (key2224, -2), (key2266, -2), (key2266, -2), (key1983, -1), (key1997, -1), (key1983, -1), (key2262, -1), (key1997, -1), (key2262, -1), (key1981, 4), (key1981, 4), (key2218, 4)]

theorem rawRowCheck17280 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form12 = rawRow17280 := by decide +kernel

def row17280 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

theorem rowCheck17280 : row17280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17280 := by decide +kernel

theorem rowEval17280 (x : Key → ℝ) : Integer.Sparse.eval row17280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17280, Integer.Sparse.eval_collectBalanced, rawRowCheck17280]

def rawRow17281 : Integer.Sparse Key := [(key1983, 2), (key1997, 2), (key1983, 2), (key1981, -2), (key1976, -2), (key1981, -2), (key2224, 2), (key2266, 2), (key2224, 2), (key1981, -1), (key1976, -1), (key2218, -1), (key1976, -1), (key2218, -1), (key1981, -1), (key2266, -2), (key2224, -2), (key2266, -2), (key1997, -1), (key1983, -1), (key2262, -1), (key1983, -1), (key2262, -1), (key1997, -1), (key1981, 4), (key2218, 4), (key1981, 4)]

theorem rawRowCheck17281 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form12 = rawRow17281 := by decide +kernel

def row17281 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

theorem rowCheck17281 : row17281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17281 := by decide +kernel

theorem rowEval17281 (x : Key → ℝ) : Integer.Sparse.eval row17281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17281, Integer.Sparse.eval_collectBalanced, rawRowCheck17281]

def rawRow17282 : Integer.Sparse Key := [(key1997, 2), (key1983, 2), (key1983, 2), (key1981, -2), (key1981, -2), (key1976, -2), (key2266, 2), (key2224, 2), (key2224, 2), (key2218, -1), (key2218, -1), (key1981, -1), (key1981, -1), (key1976, -1), (key1976, -1), (key2266, -2), (key2266, -2), (key2224, -2), (key2262, -1), (key2262, -1), (key1997, -1), (key1997, -1), (key1983, -1), (key1983, -1), (key2218, 4), (key1981, 4), (key1981, 4)]

theorem rawRowCheck17282 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form12 = rawRow17282 := by decide +kernel

def row17282 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

theorem rowCheck17282 : row17282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17282 := by decide +kernel

theorem rowEval17282 (x : Key → ℝ) : Integer.Sparse.eval row17282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17282, Integer.Sparse.eval_collectBalanced, rawRowCheck17282]

def rawRow17283 : Integer.Sparse Key := [(key2218, 2), (key2218, 2), (key2262, 2), (key2218, -2), (key2262, -2), (key2262, -2), (key1981, 2), (key1981, 2), (key1997, 2), (key1981, -1), (key1997, -1), (key1981, -1), (key2266, -1), (key1997, -1), (key2266, -1), (key1976, -2), (key1983, -2), (key1983, -2), (key1976, -1), (key1983, -1), (key1976, -1), (key2224, -1), (key1983, -1), (key2224, -1), (key1983, 4), (key1983, 4), (key2224, 4)]

theorem rawRowCheck17283 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form12 = rawRow17283 := by decide +kernel

def row17283 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

theorem rowCheck17283 : row17283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17283 := by decide +kernel

theorem rowEval17283 (x : Key → ℝ) : Integer.Sparse.eval row17283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck17283, Integer.Sparse.eval_collectBalanced, rawRowCheck17283]

def rawRow17284 : Integer.Sparse Key := [(key2218, 2), (key2262, 2), (key2218, 2), (key2262, -2), (key2218, -2), (key2262, -2), (key1981, 2), (key1997, 2), (key1981, 2), (key1997, -1), (key1981, -1), (key2266, -1), (key1981, -1), (key2266, -1), (key1997, -1), (key1983, -2), (key1976, -2), (key1983, -2), (key1983, -1), (key1976, -1), (key2224, -1), (key1976, -1), (key2224, -1), (key1983, -1), (key1983, 4), (key2224, 4), (key1983, 4)]

theorem rawRowCheck17284 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form12 = rawRow17284 := by decide +kernel

def row17284 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

theorem rowCheck17284 : row17284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17284 := by decide +kernel

theorem rowEval17284 (x : Key → ℝ) : Integer.Sparse.eval row17284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17284, Integer.Sparse.eval_collectBalanced, rawRowCheck17284]

def rawRow17285 : Integer.Sparse Key := [(key2262, 2), (key2218, 2), (key2218, 2), (key2262, -2), (key2262, -2), (key2218, -2), (key1997, 2), (key1981, 2), (key1981, 2), (key2266, -1), (key2266, -1), (key1997, -1), (key1997, -1), (key1981, -1), (key1981, -1), (key1983, -2), (key1983, -2), (key1976, -2), (key2224, -1), (key2224, -1), (key1983, -1), (key1983, -1), (key1976, -1), (key1976, -1), (key2224, 4), (key1983, 4), (key1983, 4)]

theorem rawRowCheck17285 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form12 = rawRow17285 := by decide +kernel

def row17285 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

theorem rowCheck17285 : row17285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17285 := by decide +kernel

theorem rowEval17285 (x : Key → ℝ) : Integer.Sparse.eval row17285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17285, Integer.Sparse.eval_collectBalanced, rawRowCheck17285]

def rawRow17286 : Integer.Sparse Key := [(key2262, 2), (key2262, 2), (key2262, 2), (key2218, -2), (key2218, -2), (key2218, -2), (key2266, 2), (key2266, 2), (key2266, 2), (key1981, -1), (key1981, -1), (key1981, -1), (key1981, -1), (key1981, -1), (key1981, -1), (key2224, -2), (key2224, -2), (key2224, -2), (key1983, -1), (key1983, -1), (key1983, -1), (key1983, -1), (key1983, -1), (key1983, -1), (key1976, 4), (key1976, 4), (key1976, 4)]

theorem rawRowCheck17286 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form12 = rawRow17286 := by decide +kernel

def row17286 : Integer.Sparse Key := [(key1976, 12), (key1981, -6), (key1983, -6), (key2218, -6), (key2224, -6), (key2262, 6), (key2266, 6)]

theorem rowCheck17286 : row17286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17286 := by decide +kernel

theorem rowEval17286 (x : Key → ℝ) : Integer.Sparse.eval row17286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17286, Integer.Sparse.eval_collectBalanced, rawRowCheck17286]

def rawRow17287 : Integer.Sparse Key := [(key2224, 2), (key2224, 2), (key2266, 2), (key2224, -2), (key2266, -2), (key2266, -2), (key1983, 2), (key1983, 2), (key1997, 2), (key1983, -1), (key1997, -1), (key1983, -1), (key2262, -1), (key1997, -1), (key2262, -1), (key1976, -2), (key1981, -2), (key1981, -2), (key1976, -1), (key1981, -1), (key1976, -1), (key2218, -1), (key1981, -1), (key2218, -1), (key1981, 4), (key1981, 4), (key2218, 4)]

theorem rawRowCheck17287 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form12 = rawRow17287 := by decide +kernel

def row17287 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

theorem rowCheck17287 : row17287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17287 := by decide +kernel

theorem rowEval17287 (x : Key → ℝ) : Integer.Sparse.eval row17287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17287, Integer.Sparse.eval_collectBalanced, rawRowCheck17287]

def rawRow17288 : Integer.Sparse Key := [(key2224, 2), (key2266, 2), (key2224, 2), (key2266, -2), (key2224, -2), (key2266, -2), (key1983, 2), (key1997, 2), (key1983, 2), (key1997, -1), (key1983, -1), (key2262, -1), (key1983, -1), (key2262, -1), (key1997, -1), (key1981, -2), (key1976, -2), (key1981, -2), (key1981, -1), (key1976, -1), (key2218, -1), (key1976, -1), (key2218, -1), (key1981, -1), (key1981, 4), (key2218, 4), (key1981, 4)]

theorem rawRowCheck17288 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form12 = rawRow17288 := by decide +kernel

def row17288 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

theorem rowCheck17288 : row17288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17288 := by decide +kernel

theorem rowEval17288 (x : Key → ℝ) : Integer.Sparse.eval row17288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17288, Integer.Sparse.eval_collectBalanced, rawRowCheck17288]

def rawRow17289 : Integer.Sparse Key := [(key2266, 2), (key2224, 2), (key2224, 2), (key2266, -2), (key2266, -2), (key2224, -2), (key1997, 2), (key1983, 2), (key1983, 2), (key2262, -1), (key2262, -1), (key1997, -1), (key1997, -1), (key1983, -1), (key1983, -1), (key1981, -2), (key1981, -2), (key1976, -2), (key2218, -1), (key2218, -1), (key1981, -1), (key1981, -1), (key1976, -1), (key1976, -1), (key2218, 4), (key1981, 4), (key1981, 4)]

theorem rawRowCheck17289 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form12 = rawRow17289 := by decide +kernel

def row17289 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

theorem rowCheck17289 : row17289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17289 := by decide +kernel

theorem rowEval17289 (x : Key → ℝ) : Integer.Sparse.eval row17289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17289, Integer.Sparse.eval_collectBalanced, rawRowCheck17289]

def rawRow17290 : Integer.Sparse Key := [(key2266, 2), (key2266, 2), (key2266, 2), (key2224, -2), (key2224, -2), (key2224, -2), (key2262, 2), (key2262, 2), (key2262, 2), (key1983, -1), (key1983, -1), (key1983, -1), (key1983, -1), (key1983, -1), (key1983, -1), (key2218, -2), (key2218, -2), (key2218, -2), (key1981, -1), (key1981, -1), (key1981, -1), (key1981, -1), (key1981, -1), (key1981, -1), (key1976, 4), (key1976, 4), (key1976, 4)]

theorem rawRowCheck17290 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form12 = rawRow17290 := by decide +kernel

def row17290 : Integer.Sparse Key := [(key1976, 12), (key1981, -6), (key1983, -6), (key2218, -6), (key2224, -6), (key2262, 6), (key2266, 6)]

theorem rowCheck17290 : row17290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17290 := by decide +kernel

theorem rowEval17290 (x : Key → ℝ) : Integer.Sparse.eval row17290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17290, Integer.Sparse.eval_collectBalanced, rawRowCheck17290]

def rawRow17291 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, 2), (key2013, -1), (key2019, -1), (key2042, -1), (key2047, -1), (key2055, -1), (key2056, -1), (key2013, 2), (key2019, 2), (key2026, 2), (key2013, -1), (key2019, -1), (key2127, -1), (key2134, -1), (key2144, -1), (key2145, -1), (key2013, -1), (key2019, -1), (key2042, -1), (key2047, -1), (key2055, -1), (key2056, -1), (key2013, -1), (key2019, -1), (key2127, -1), (key2134, -1), (key2144, -1), (key2145, -1), (key2042, 2), (key2047, 2), (key2127, 2), (key2134, 2), (key2228, 2), (key2229, 2)]

theorem rawRowCheck17291 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form13 = rawRow17291 := by decide +kernel

def row17291 : Integer.Sparse Key := [(key2026, 4), (key2055, -2), (key2056, -2), (key2144, -2), (key2145, -2), (key2228, 2), (key2229, 2)]

theorem rowCheck17291 : row17291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17291 := by decide +kernel

theorem rowEval17291 (x : Key → ℝ) : Integer.Sparse.eval row17291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck17291, Integer.Sparse.eval_collectBalanced, rawRowCheck17291]

def rawRow17292 : Integer.Sparse Key := [(key2019, 2), (key2013, 2), (key2026, 2), (key2019, -1), (key2013, -1), (key2047, -1), (key2042, -1), (key2056, -1), (key2055, -1), (key2019, 2), (key2013, 2), (key2026, 2), (key2019, -1), (key2013, -1), (key2134, -1), (key2127, -1), (key2145, -1), (key2144, -1), (key2019, -1), (key2013, -1), (key2047, -1), (key2042, -1), (key2056, -1), (key2055, -1), (key2019, -1), (key2013, -1), (key2134, -1), (key2127, -1), (key2145, -1), (key2144, -1), (key2047, 2), (key2042, 2), (key2134, 2), (key2127, 2), (key2229, 2), (key2228, 2)]

theorem rawRowCheck17292 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form13 = rawRow17292 := by decide +kernel

def row17292 : Integer.Sparse Key := [(key2026, 4), (key2055, -2), (key2056, -2), (key2144, -2), (key2145, -2), (key2228, 2), (key2229, 2)]

theorem rowCheck17292 : row17292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17292 := by decide +kernel

theorem rowEval17292 (x : Key → ℝ) : Integer.Sparse.eval row17292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17292, Integer.Sparse.eval_collectBalanced, rawRowCheck17292]

def rawRow17293 : Integer.Sparse Key := [(key2013, 2), (key2026, 2), (key2019, 2), (key2042, -1), (key2055, -1), (key2013, -1), (key2056, -1), (key2019, -1), (key2047, -1), (key2013, 2), (key2026, 2), (key2019, 2), (key2127, -1), (key2144, -1), (key2013, -1), (key2145, -1), (key2019, -1), (key2134, -1), (key2042, -1), (key2055, -1), (key2013, -1), (key2056, -1), (key2019, -1), (key2047, -1), (key2127, -1), (key2144, -1), (key2013, -1), (key2145, -1), (key2019, -1), (key2134, -1), (key2127, 2), (key2228, 2), (key2042, 2), (key2229, 2), (key2047, 2), (key2134, 2)]

theorem rawRowCheck17293 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form13 = rawRow17293 := by decide +kernel

def row17293 : Integer.Sparse Key := [(key2026, 4), (key2055, -2), (key2056, -2), (key2144, -2), (key2145, -2), (key2228, 2), (key2229, 2)]

theorem rowCheck17293 : row17293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17293 := by decide +kernel

theorem rowEval17293 (x : Key → ℝ) : Integer.Sparse.eval row17293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck17293, Integer.Sparse.eval_collectBalanced, rawRowCheck17293]

def rawRow17294 : Integer.Sparse Key := [(key2026, 2), (key2013, 2), (key2019, 2), (key2055, -1), (key2042, -1), (key2056, -1), (key2013, -1), (key2047, -1), (key2019, -1), (key2026, 2), (key2013, 2), (key2019, 2), (key2144, -1), (key2127, -1), (key2145, -1), (key2013, -1), (key2134, -1), (key2019, -1), (key2055, -1), (key2042, -1), (key2056, -1), (key2013, -1), (key2047, -1), (key2019, -1), (key2144, -1), (key2127, -1), (key2145, -1), (key2013, -1), (key2134, -1), (key2019, -1), (key2228, 2), (key2127, 2), (key2229, 2), (key2042, 2), (key2134, 2), (key2047, 2)]

theorem rawRowCheck17294 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form13 = rawRow17294 := by decide +kernel

def row17294 : Integer.Sparse Key := [(key2026, 4), (key2055, -2), (key2056, -2), (key2144, -2), (key2145, -2), (key2228, 2), (key2229, 2)]

theorem rowCheck17294 : row17294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17294 := by decide +kernel

theorem rowEval17294 (x : Key → ℝ) : Integer.Sparse.eval row17294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17294, Integer.Sparse.eval_collectBalanced, rawRowCheck17294]

def rawRow17295 : Integer.Sparse Key := [(key2019, 2), (key2026, 2), (key2013, 2), (key2047, -1), (key2056, -1), (key2019, -1), (key2055, -1), (key2013, -1), (key2042, -1), (key2019, 2), (key2026, 2), (key2013, 2), (key2134, -1), (key2145, -1), (key2019, -1), (key2144, -1), (key2013, -1), (key2127, -1), (key2047, -1), (key2056, -1), (key2019, -1), (key2055, -1), (key2013, -1), (key2042, -1), (key2134, -1), (key2145, -1), (key2019, -1), (key2144, -1), (key2013, -1), (key2127, -1), (key2134, 2), (key2229, 2), (key2047, 2), (key2228, 2), (key2042, 2), (key2127, 2)]

theorem rawRowCheck17295 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form13 = rawRow17295 := by decide +kernel

def row17295 : Integer.Sparse Key := [(key2026, 4), (key2055, -2), (key2056, -2), (key2144, -2), (key2145, -2), (key2228, 2), (key2229, 2)]

theorem rowCheck17295 : row17295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17295 := by decide +kernel

theorem rowEval17295 (x : Key → ℝ) : Integer.Sparse.eval row17295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17295, Integer.Sparse.eval_collectBalanced, rawRowCheck17295]

def rawRow17296 : Integer.Sparse Key := [(key2026, 2), (key2019, 2), (key2013, 2), (key2056, -1), (key2047, -1), (key2055, -1), (key2019, -1), (key2042, -1), (key2013, -1), (key2026, 2), (key2019, 2), (key2013, 2), (key2145, -1), (key2134, -1), (key2144, -1), (key2019, -1), (key2127, -1), (key2013, -1), (key2056, -1), (key2047, -1), (key2055, -1), (key2019, -1), (key2042, -1), (key2013, -1), (key2145, -1), (key2134, -1), (key2144, -1), (key2019, -1), (key2127, -1), (key2013, -1), (key2229, 2), (key2134, 2), (key2228, 2), (key2047, 2), (key2127, 2), (key2042, 2)]

theorem rawRowCheck17296 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form13 = rawRow17296 := by decide +kernel

def row17296 : Integer.Sparse Key := [(key2026, 4), (key2055, -2), (key2056, -2), (key2144, -2), (key2145, -2), (key2228, 2), (key2229, 2)]

theorem rowCheck17296 : row17296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17296 := by decide +kernel

theorem rowEval17296 (x : Key → ℝ) : Integer.Sparse.eval row17296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17296, Integer.Sparse.eval_collectBalanced, rawRowCheck17296]

def rawRow17297 : Integer.Sparse Key := [(key2042, 2), (key2055, 2), (key2055, 2), (key2013, -1), (key2026, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2056, -1), (key2127, 2), (key2144, 2), (key2144, 2), (key2013, -1), (key2026, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2145, -1), (key2127, -1), (key2144, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2228, -1), (key2042, -1), (key2055, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2229, -1), (key2013, 2), (key2056, 2), (key2013, 2), (key2145, 2), (key2056, 2), (key2145, 2)]

theorem rawRowCheck17297 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form13 = rawRow17297 := by decide +kernel

def row17297 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

theorem rowCheck17297 : row17297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17297 := by decide +kernel

theorem rowEval17297 (x : Key → ℝ) : Integer.Sparse.eval row17297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck17297, Integer.Sparse.eval_collectBalanced, rawRowCheck17297]

def rawRow17298 : Integer.Sparse Key := [(key2055, 2), (key2042, 2), (key2055, 2), (key2026, -1), (key2013, -1), (key2056, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2144, 2), (key2127, 2), (key2144, 2), (key2026, -1), (key2013, -1), (key2145, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2144, -1), (key2127, -1), (key2228, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2055, -1), (key2042, -1), (key2229, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2056, 2), (key2013, 2), (key2145, 2), (key2013, 2), (key2145, 2), (key2056, 2)]

theorem rawRowCheck17298 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form13 = rawRow17298 := by decide +kernel

def row17298 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

theorem rowCheck17298 : row17298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17298 := by decide +kernel

theorem rowEval17298 (x : Key → ℝ) : Integer.Sparse.eval row17298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17298, Integer.Sparse.eval_collectBalanced, rawRowCheck17298]

def rawRow17299 : Integer.Sparse Key := [(key2055, 2), (key2055, 2), (key2042, 2), (key2056, -1), (key2056, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2144, 2), (key2144, 2), (key2127, 2), (key2145, -1), (key2145, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2228, -1), (key2228, -1), (key2144, -1), (key2144, -1), (key2127, -1), (key2127, -1), (key2229, -1), (key2229, -1), (key2055, -1), (key2055, -1), (key2042, -1), (key2042, -1), (key2145, 2), (key2145, 2), (key2056, 2), (key2056, 2), (key2013, 2), (key2013, 2)]

theorem rawRowCheck17299 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form13 = rawRow17299 := by decide +kernel

def row17299 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

theorem rowCheck17299 : row17299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17299 := by decide +kernel

theorem rowEval17299 (x : Key → ℝ) : Integer.Sparse.eval row17299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17299, Integer.Sparse.eval_collectBalanced, rawRowCheck17299]

def rawRow17300 : Integer.Sparse Key := [(key2047, 2), (key2056, 2), (key2056, 2), (key2019, -1), (key2026, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2055, -1), (key2134, 2), (key2145, 2), (key2145, 2), (key2019, -1), (key2026, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2144, -1), (key2134, -1), (key2145, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2229, -1), (key2047, -1), (key2056, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2228, -1), (key2019, 2), (key2055, 2), (key2019, 2), (key2144, 2), (key2055, 2), (key2144, 2)]

theorem rawRowCheck17300 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form13 = rawRow17300 := by decide +kernel

def row17300 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

theorem rowCheck17300 : row17300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17300 := by decide +kernel

theorem rowEval17300 (x : Key → ℝ) : Integer.Sparse.eval row17300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17300, Integer.Sparse.eval_collectBalanced, rawRowCheck17300]

def rawRow17301 : Integer.Sparse Key := [(key2056, 2), (key2047, 2), (key2056, 2), (key2026, -1), (key2019, -1), (key2055, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2145, 2), (key2134, 2), (key2145, 2), (key2026, -1), (key2019, -1), (key2144, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2145, -1), (key2134, -1), (key2229, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2056, -1), (key2047, -1), (key2228, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2055, 2), (key2019, 2), (key2144, 2), (key2019, 2), (key2144, 2), (key2055, 2)]

theorem rawRowCheck17301 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form13 = rawRow17301 := by decide +kernel

def row17301 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

theorem rowCheck17301 : row17301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17301 := by decide +kernel

theorem rowEval17301 (x : Key → ℝ) : Integer.Sparse.eval row17301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17301, Integer.Sparse.eval_collectBalanced, rawRowCheck17301]

def rawRow17302 : Integer.Sparse Key := [(key2056, 2), (key2056, 2), (key2047, 2), (key2055, -1), (key2055, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2145, 2), (key2145, 2), (key2134, 2), (key2144, -1), (key2144, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2229, -1), (key2229, -1), (key2145, -1), (key2145, -1), (key2134, -1), (key2134, -1), (key2228, -1), (key2228, -1), (key2056, -1), (key2056, -1), (key2047, -1), (key2047, -1), (key2144, 2), (key2144, 2), (key2055, 2), (key2055, 2), (key2019, 2), (key2019, 2)]

theorem rawRowCheck17302 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form13 = rawRow17302 := by decide +kernel

def row17302 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

theorem rowCheck17302 : row17302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17302 := by decide +kernel

theorem rowEval17302 (x : Key → ℝ) : Integer.Sparse.eval row17302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17302, Integer.Sparse.eval_collectBalanced, rawRowCheck17302]

def rawRow17303 : Integer.Sparse Key := [(key2127, 2), (key2144, 2), (key2144, 2), (key2127, -1), (key2144, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2228, -1), (key2042, 2), (key2055, 2), (key2055, 2), (key2042, -1), (key2055, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2229, -1), (key2013, -1), (key2026, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2056, -1), (key2013, -1), (key2026, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2145, -1), (key2013, 2), (key2056, 2), (key2013, 2), (key2145, 2), (key2056, 2), (key2145, 2)]

theorem rawRowCheck17303 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form13 = rawRow17303 := by decide +kernel

def row17303 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

theorem rowCheck17303 : row17303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17303 := by decide +kernel

theorem rowEval17303 (x : Key → ℝ) : Integer.Sparse.eval row17303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form13) x := by
  rw [rowCheck17303, Integer.Sparse.eval_collectBalanced, rawRowCheck17303]

def rawRow17304 : Integer.Sparse Key := [(key2144, 2), (key2127, 2), (key2144, 2), (key2144, -1), (key2127, -1), (key2228, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2055, 2), (key2042, 2), (key2055, 2), (key2055, -1), (key2042, -1), (key2229, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2026, -1), (key2013, -1), (key2056, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2145, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2056, 2), (key2013, 2), (key2145, 2), (key2013, 2), (key2145, 2), (key2056, 2)]

theorem rawRowCheck17304 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form13 = rawRow17304 := by decide +kernel

def row17304 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

theorem rowCheck17304 : row17304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17304 := by decide +kernel

theorem rowEval17304 (x : Key → ℝ) : Integer.Sparse.eval row17304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17304, Integer.Sparse.eval_collectBalanced, rawRowCheck17304]

def rawRow17305 : Integer.Sparse Key := [(key2144, 2), (key2144, 2), (key2127, 2), (key2228, -1), (key2228, -1), (key2144, -1), (key2144, -1), (key2127, -1), (key2127, -1), (key2055, 2), (key2055, 2), (key2042, 2), (key2229, -1), (key2229, -1), (key2055, -1), (key2055, -1), (key2042, -1), (key2042, -1), (key2056, -1), (key2056, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2145, -1), (key2145, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2145, 2), (key2145, 2), (key2056, 2), (key2056, 2), (key2013, 2), (key2013, 2)]

theorem rawRowCheck17305 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form13 = rawRow17305 := by decide +kernel

def row17305 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

theorem rowCheck17305 : row17305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17305 := by decide +kernel

theorem rowEval17305 (x : Key → ℝ) : Integer.Sparse.eval row17305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17305, Integer.Sparse.eval_collectBalanced, rawRowCheck17305]

def rawRow17306 : Integer.Sparse Key := [(key2228, 2), (key2228, 2), (key2228, 2), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2229, 2), (key2229, 2), (key2229, 2), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2)]

theorem rawRowCheck17306 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form13 = rawRow17306 := by decide +kernel

def row17306 : Integer.Sparse Key := [(key2026, 12), (key2055, -6), (key2056, -6), (key2144, -6), (key2145, -6), (key2228, 6), (key2229, 6)]

theorem rowCheck17306 : row17306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17306 := by decide +kernel

theorem rowEval17306 (x : Key → ℝ) : Integer.Sparse.eval row17306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17306, Integer.Sparse.eval_collectBalanced, rawRowCheck17306]

def rawRow17307 : Integer.Sparse Key := [(key2134, 2), (key2145, 2), (key2145, 2), (key2134, -1), (key2145, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2229, -1), (key2047, 2), (key2056, 2), (key2056, 2), (key2047, -1), (key2056, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2228, -1), (key2019, -1), (key2026, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2055, -1), (key2019, -1), (key2026, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2144, -1), (key2019, 2), (key2055, 2), (key2019, 2), (key2144, 2), (key2055, 2), (key2144, 2)]

theorem rawRowCheck17307 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form13 = rawRow17307 := by decide +kernel

def row17307 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

theorem rowCheck17307 : row17307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17307 := by decide +kernel

theorem rowEval17307 (x : Key → ℝ) : Integer.Sparse.eval row17307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck17307, Integer.Sparse.eval_collectBalanced, rawRowCheck17307]

def rawRow17308 : Integer.Sparse Key := [(key2145, 2), (key2134, 2), (key2145, 2), (key2145, -1), (key2134, -1), (key2229, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2056, 2), (key2047, 2), (key2056, 2), (key2056, -1), (key2047, -1), (key2228, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2026, -1), (key2019, -1), (key2055, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2144, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2055, 2), (key2019, 2), (key2144, 2), (key2019, 2), (key2144, 2), (key2055, 2)]

theorem rawRowCheck17308 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form13 = rawRow17308 := by decide +kernel

def row17308 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

theorem rowCheck17308 : row17308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17308 := by decide +kernel

theorem rowEval17308 (x : Key → ℝ) : Integer.Sparse.eval row17308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17308, Integer.Sparse.eval_collectBalanced, rawRowCheck17308]

def rawRow17309 : Integer.Sparse Key := [(key2145, 2), (key2145, 2), (key2134, 2), (key2229, -1), (key2229, -1), (key2145, -1), (key2145, -1), (key2134, -1), (key2134, -1), (key2056, 2), (key2056, 2), (key2047, 2), (key2228, -1), (key2228, -1), (key2056, -1), (key2056, -1), (key2047, -1), (key2047, -1), (key2055, -1), (key2055, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2144, -1), (key2144, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2144, 2), (key2144, 2), (key2055, 2), (key2055, 2), (key2019, 2), (key2019, 2)]

theorem rawRowCheck17309 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form13 = rawRow17309 := by decide +kernel

def row17309 : Integer.Sparse Key := [(key2026, -4), (key2055, 2), (key2056, 2), (key2144, 2), (key2145, 2), (key2228, -2), (key2229, -2)]

theorem rowCheck17309 : row17309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17309 := by decide +kernel

theorem rowEval17309 (x : Key → ℝ) : Integer.Sparse.eval row17309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17309, Integer.Sparse.eval_collectBalanced, rawRowCheck17309]

def rawRow17310 : Integer.Sparse Key := [(key2229, 2), (key2229, 2), (key2229, 2), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2228, 2), (key2228, 2), (key2228, 2), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2)]

theorem rawRowCheck17310 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form13 = rawRow17310 := by decide +kernel

def row17310 : Integer.Sparse Key := [(key2026, 12), (key2055, -6), (key2056, -6), (key2144, -6), (key2145, -6), (key2228, 6), (key2229, 6)]

theorem rowCheck17310 : row17310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17310 := by decide +kernel

theorem rowEval17310 (x : Key → ℝ) : Integer.Sparse.eval row17310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck17310, Integer.Sparse.eval_collectBalanced, rawRowCheck17310]

def rawRow17311 : Integer.Sparse Key := [(key2013, -1), (key2019, -1), (key2042, -1), (key2047, -1), (key2055, -1), (key2056, -1), (key2026, 2), (key2055, 2), (key2056, 2), (key2013, 1), (key2019, 1), (key2127, 1), (key2134, 1), (key2144, 1), (key2145, 1), (key2026, -2), (key2144, -2), (key2145, -2), (key2013, -1), (key2019, -1), (key2042, -1), (key2047, -1), (key2055, -1), (key2056, -1), (key2013, 1), (key2019, 1), (key2127, 1), (key2134, 1), (key2144, 1), (key2145, 1), (key2026, 2), (key2055, 2), (key2056, 2), (key2026, -2), (key2144, -2), (key2145, -2)]

theorem rawRowCheck17311 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form14 = rawRow17311 := by decide +kernel

def row17311 : Integer.Sparse Key := [(key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2), (key2127, 2), (key2134, 2), (key2144, -2), (key2145, -2)]

theorem rowCheck17311 : row17311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17311 := by decide +kernel

theorem rowEval17311 (x : Key → ℝ) : Integer.Sparse.eval row17311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form14) x := by
  rw [rowCheck17311, Integer.Sparse.eval_collectBalanced, rawRowCheck17311]

def rawRow17312 : Integer.Sparse Key := [(key2019, -1), (key2013, -1), (key2047, -1), (key2042, -1), (key2056, -1), (key2055, -1), (key2026, 2), (key2056, 2), (key2055, 2), (key2019, 1), (key2013, 1), (key2134, 1), (key2127, 1), (key2145, 1), (key2144, 1), (key2026, -2), (key2145, -2), (key2144, -2), (key2019, -1), (key2013, -1), (key2047, -1), (key2042, -1), (key2056, -1), (key2055, -1), (key2019, 1), (key2013, 1), (key2134, 1), (key2127, 1), (key2145, 1), (key2144, 1), (key2026, 2), (key2056, 2), (key2055, 2), (key2026, -2), (key2145, -2), (key2144, -2)]

theorem rawRowCheck17312 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form14 = rawRow17312 := by decide +kernel

def row17312 : Integer.Sparse Key := [(key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2), (key2127, 2), (key2134, 2), (key2144, -2), (key2145, -2)]

theorem rowCheck17312 : row17312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17312 := by decide +kernel

theorem rowEval17312 (x : Key → ℝ) : Integer.Sparse.eval row17312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17312, Integer.Sparse.eval_collectBalanced, rawRowCheck17312]

def rawRow17313 : Integer.Sparse Key := [(key2042, -1), (key2055, -1), (key2013, -1), (key2056, -1), (key2019, -1), (key2047, -1), (key2055, 2), (key2026, 2), (key2056, 2), (key2127, 1), (key2144, 1), (key2013, 1), (key2145, 1), (key2019, 1), (key2134, 1), (key2144, -2), (key2026, -2), (key2145, -2), (key2042, -1), (key2055, -1), (key2013, -1), (key2056, -1), (key2019, -1), (key2047, -1), (key2127, 1), (key2144, 1), (key2013, 1), (key2145, 1), (key2019, 1), (key2134, 1), (key2055, 2), (key2026, 2), (key2056, 2), (key2144, -2), (key2026, -2), (key2145, -2)]

theorem rawRowCheck17313 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form14 = rawRow17313 := by decide +kernel

def row17313 : Integer.Sparse Key := [(key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2), (key2127, 2), (key2134, 2), (key2144, -2), (key2145, -2)]

theorem rowCheck17313 : row17313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17313 := by decide +kernel

theorem rowEval17313 (x : Key → ℝ) : Integer.Sparse.eval row17313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form14) x := by
  rw [rowCheck17313, Integer.Sparse.eval_collectBalanced, rawRowCheck17313]

def rawRow17314 : Integer.Sparse Key := [(key2055, -1), (key2042, -1), (key2056, -1), (key2013, -1), (key2047, -1), (key2019, -1), (key2055, 2), (key2056, 2), (key2026, 2), (key2144, 1), (key2127, 1), (key2145, 1), (key2013, 1), (key2134, 1), (key2019, 1), (key2144, -2), (key2145, -2), (key2026, -2), (key2055, -1), (key2042, -1), (key2056, -1), (key2013, -1), (key2047, -1), (key2019, -1), (key2144, 1), (key2127, 1), (key2145, 1), (key2013, 1), (key2134, 1), (key2019, 1), (key2055, 2), (key2056, 2), (key2026, 2), (key2144, -2), (key2145, -2), (key2026, -2)]

theorem rawRowCheck17314 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form14 = rawRow17314 := by decide +kernel

def row17314 : Integer.Sparse Key := [(key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2), (key2127, 2), (key2134, 2), (key2144, -2), (key2145, -2)]

theorem rowCheck17314 : row17314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17314 := by decide +kernel

theorem rowEval17314 (x : Key → ℝ) : Integer.Sparse.eval row17314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17314, Integer.Sparse.eval_collectBalanced, rawRowCheck17314]

def rawRow17315 : Integer.Sparse Key := [(key2047, -1), (key2056, -1), (key2019, -1), (key2055, -1), (key2013, -1), (key2042, -1), (key2056, 2), (key2026, 2), (key2055, 2), (key2134, 1), (key2145, 1), (key2019, 1), (key2144, 1), (key2013, 1), (key2127, 1), (key2145, -2), (key2026, -2), (key2144, -2), (key2047, -1), (key2056, -1), (key2019, -1), (key2055, -1), (key2013, -1), (key2042, -1), (key2134, 1), (key2145, 1), (key2019, 1), (key2144, 1), (key2013, 1), (key2127, 1), (key2056, 2), (key2026, 2), (key2055, 2), (key2145, -2), (key2026, -2), (key2144, -2)]

theorem rawRowCheck17315 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form14 = rawRow17315 := by decide +kernel

def row17315 : Integer.Sparse Key := [(key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2), (key2127, 2), (key2134, 2), (key2144, -2), (key2145, -2)]

theorem rowCheck17315 : row17315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17315 := by decide +kernel

theorem rowEval17315 (x : Key → ℝ) : Integer.Sparse.eval row17315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17315, Integer.Sparse.eval_collectBalanced, rawRowCheck17315]

def rawRow17316 : Integer.Sparse Key := [(key2056, -1), (key2047, -1), (key2055, -1), (key2019, -1), (key2042, -1), (key2013, -1), (key2056, 2), (key2055, 2), (key2026, 2), (key2145, 1), (key2134, 1), (key2144, 1), (key2019, 1), (key2127, 1), (key2013, 1), (key2145, -2), (key2144, -2), (key2026, -2), (key2056, -1), (key2047, -1), (key2055, -1), (key2019, -1), (key2042, -1), (key2013, -1), (key2145, 1), (key2134, 1), (key2144, 1), (key2019, 1), (key2127, 1), (key2013, 1), (key2056, 2), (key2055, 2), (key2026, 2), (key2145, -2), (key2144, -2), (key2026, -2)]

theorem rawRowCheck17316 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form14 = rawRow17316 := by decide +kernel

def row17316 : Integer.Sparse Key := [(key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2), (key2127, 2), (key2134, 2), (key2144, -2), (key2145, -2)]

theorem rowCheck17316 : row17316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17316 := by decide +kernel

theorem rowEval17316 (x : Key → ℝ) : Integer.Sparse.eval row17316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17316, Integer.Sparse.eval_collectBalanced, rawRowCheck17316]

def rawRow17317 : Integer.Sparse Key := [(key2013, -1), (key2026, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2056, -1), (key2019, 2), (key2019, 2), (key2047, 2), (key2013, 1), (key2026, 1), (key2013, 1), (key2145, 1), (key2026, 1), (key2145, 1), (key2019, -2), (key2019, -2), (key2134, -2), (key2127, -1), (key2144, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2228, -1), (key2042, 1), (key2055, 1), (key2042, 1), (key2229, 1), (key2055, 1), (key2229, 1), (key2144, 2), (key2144, 2), (key2228, 2), (key2055, -2), (key2055, -2), (key2229, -2)]

theorem rawRowCheck17317 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form14 = rawRow17317 := by decide +kernel

def row17317 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

theorem rowCheck17317 : row17317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17317 := by decide +kernel

theorem rowEval17317 (x : Key → ℝ) : Integer.Sparse.eval row17317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form14) x := by
  rw [rowCheck17317, Integer.Sparse.eval_collectBalanced, rawRowCheck17317]

def rawRow17318 : Integer.Sparse Key := [(key2026, -1), (key2013, -1), (key2056, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2019, 2), (key2047, 2), (key2019, 2), (key2026, 1), (key2013, 1), (key2145, 1), (key2013, 1), (key2145, 1), (key2026, 1), (key2019, -2), (key2134, -2), (key2019, -2), (key2144, -1), (key2127, -1), (key2228, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2055, 1), (key2042, 1), (key2229, 1), (key2042, 1), (key2229, 1), (key2055, 1), (key2144, 2), (key2228, 2), (key2144, 2), (key2055, -2), (key2229, -2), (key2055, -2)]

theorem rawRowCheck17318 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form14 = rawRow17318 := by decide +kernel

def row17318 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

theorem rowCheck17318 : row17318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17318 := by decide +kernel

theorem rowEval17318 (x : Key → ℝ) : Integer.Sparse.eval row17318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17318, Integer.Sparse.eval_collectBalanced, rawRowCheck17318]

def rawRow17319 : Integer.Sparse Key := [(key2056, -1), (key2056, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2047, 2), (key2019, 2), (key2019, 2), (key2145, 1), (key2145, 1), (key2026, 1), (key2026, 1), (key2013, 1), (key2013, 1), (key2134, -2), (key2019, -2), (key2019, -2), (key2228, -1), (key2228, -1), (key2144, -1), (key2144, -1), (key2127, -1), (key2127, -1), (key2229, 1), (key2229, 1), (key2055, 1), (key2055, 1), (key2042, 1), (key2042, 1), (key2228, 2), (key2144, 2), (key2144, 2), (key2229, -2), (key2055, -2), (key2055, -2)]

theorem rawRowCheck17319 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form14 = rawRow17319 := by decide +kernel

def row17319 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

theorem rowCheck17319 : row17319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17319 := by decide +kernel

theorem rowEval17319 (x : Key → ℝ) : Integer.Sparse.eval row17319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17319, Integer.Sparse.eval_collectBalanced, rawRowCheck17319]

def rawRow17320 : Integer.Sparse Key := [(key2019, -1), (key2026, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2055, -1), (key2013, 2), (key2013, 2), (key2042, 2), (key2019, 1), (key2026, 1), (key2019, 1), (key2144, 1), (key2026, 1), (key2144, 1), (key2013, -2), (key2013, -2), (key2127, -2), (key2134, -1), (key2145, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2229, -1), (key2047, 1), (key2056, 1), (key2047, 1), (key2228, 1), (key2056, 1), (key2228, 1), (key2145, 2), (key2145, 2), (key2229, 2), (key2056, -2), (key2056, -2), (key2228, -2)]

theorem rawRowCheck17320 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form14 = rawRow17320 := by decide +kernel

def row17320 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

theorem rowCheck17320 : row17320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17320 := by decide +kernel

theorem rowEval17320 (x : Key → ℝ) : Integer.Sparse.eval row17320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17320, Integer.Sparse.eval_collectBalanced, rawRowCheck17320]

def rawRow17321 : Integer.Sparse Key := [(key2026, -1), (key2019, -1), (key2055, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2013, 2), (key2042, 2), (key2013, 2), (key2026, 1), (key2019, 1), (key2144, 1), (key2019, 1), (key2144, 1), (key2026, 1), (key2013, -2), (key2127, -2), (key2013, -2), (key2145, -1), (key2134, -1), (key2229, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2056, 1), (key2047, 1), (key2228, 1), (key2047, 1), (key2228, 1), (key2056, 1), (key2145, 2), (key2229, 2), (key2145, 2), (key2056, -2), (key2228, -2), (key2056, -2)]

theorem rawRowCheck17321 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form14 = rawRow17321 := by decide +kernel

def row17321 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

theorem rowCheck17321 : row17321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17321 := by decide +kernel

theorem rowEval17321 (x : Key → ℝ) : Integer.Sparse.eval row17321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17321, Integer.Sparse.eval_collectBalanced, rawRowCheck17321]

def rawRow17322 : Integer.Sparse Key := [(key2055, -1), (key2055, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2042, 2), (key2013, 2), (key2013, 2), (key2144, 1), (key2144, 1), (key2026, 1), (key2026, 1), (key2019, 1), (key2019, 1), (key2127, -2), (key2013, -2), (key2013, -2), (key2229, -1), (key2229, -1), (key2145, -1), (key2145, -1), (key2134, -1), (key2134, -1), (key2228, 1), (key2228, 1), (key2056, 1), (key2056, 1), (key2047, 1), (key2047, 1), (key2229, 2), (key2145, 2), (key2145, 2), (key2228, -2), (key2056, -2), (key2056, -2)]

theorem rawRowCheck17322 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form14 = rawRow17322 := by decide +kernel

def row17322 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

theorem rowCheck17322 : row17322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17322 := by decide +kernel

theorem rowEval17322 (x : Key → ℝ) : Integer.Sparse.eval row17322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17322, Integer.Sparse.eval_collectBalanced, rawRowCheck17322]

def rawRow17323 : Integer.Sparse Key := [(key2127, -1), (key2144, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2228, -1), (key2144, 2), (key2144, 2), (key2228, 2), (key2042, 1), (key2055, 1), (key2042, 1), (key2229, 1), (key2055, 1), (key2229, 1), (key2055, -2), (key2055, -2), (key2229, -2), (key2013, -1), (key2026, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2056, -1), (key2013, 1), (key2026, 1), (key2013, 1), (key2145, 1), (key2026, 1), (key2145, 1), (key2019, 2), (key2019, 2), (key2047, 2), (key2019, -2), (key2019, -2), (key2134, -2)]

theorem rawRowCheck17323 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form14 = rawRow17323 := by decide +kernel

def row17323 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

theorem rowCheck17323 : row17323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17323 := by decide +kernel

theorem rowEval17323 (x : Key → ℝ) : Integer.Sparse.eval row17323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form14) x := by
  rw [rowCheck17323, Integer.Sparse.eval_collectBalanced, rawRowCheck17323]

def rawRow17324 : Integer.Sparse Key := [(key2144, -1), (key2127, -1), (key2228, -1), (key2127, -1), (key2228, -1), (key2144, -1), (key2144, 2), (key2228, 2), (key2144, 2), (key2055, 1), (key2042, 1), (key2229, 1), (key2042, 1), (key2229, 1), (key2055, 1), (key2055, -2), (key2229, -2), (key2055, -2), (key2026, -1), (key2013, -1), (key2056, -1), (key2013, -1), (key2056, -1), (key2026, -1), (key2026, 1), (key2013, 1), (key2145, 1), (key2013, 1), (key2145, 1), (key2026, 1), (key2019, 2), (key2047, 2), (key2019, 2), (key2019, -2), (key2134, -2), (key2019, -2)]

theorem rawRowCheck17324 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form14 = rawRow17324 := by decide +kernel

def row17324 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

theorem rowCheck17324 : row17324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17324 := by decide +kernel

theorem rowEval17324 (x : Key → ℝ) : Integer.Sparse.eval row17324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17324, Integer.Sparse.eval_collectBalanced, rawRowCheck17324]

def rawRow17325 : Integer.Sparse Key := [(key2228, -1), (key2228, -1), (key2144, -1), (key2144, -1), (key2127, -1), (key2127, -1), (key2228, 2), (key2144, 2), (key2144, 2), (key2229, 1), (key2229, 1), (key2055, 1), (key2055, 1), (key2042, 1), (key2042, 1), (key2229, -2), (key2055, -2), (key2055, -2), (key2056, -1), (key2056, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2145, 1), (key2145, 1), (key2026, 1), (key2026, 1), (key2013, 1), (key2013, 1), (key2047, 2), (key2019, 2), (key2019, 2), (key2134, -2), (key2019, -2), (key2019, -2)]

theorem rawRowCheck17325 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form14 = rawRow17325 := by decide +kernel

def row17325 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

theorem rowCheck17325 : row17325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17325 := by decide +kernel

theorem rowEval17325 (x : Key → ℝ) : Integer.Sparse.eval row17325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17325, Integer.Sparse.eval_collectBalanced, rawRowCheck17325]

def rawRow17326 : Integer.Sparse Key := [(key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2127, 2), (key2127, 2), (key2127, 2), (key2055, 1), (key2055, 1), (key2055, 1), (key2055, 1), (key2055, 1), (key2055, 1), (key2042, -2), (key2042, -2), (key2042, -2), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2056, 1), (key2056, 1), (key2056, 1), (key2056, 1), (key2056, 1), (key2056, 1), (key2134, 2), (key2134, 2), (key2134, 2), (key2047, -2), (key2047, -2), (key2047, -2)]

theorem rawRowCheck17326 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form14 = rawRow17326 := by decide +kernel

def row17326 : Integer.Sparse Key := [(key2042, -6), (key2047, -6), (key2055, 6), (key2056, 6), (key2127, 6), (key2134, 6), (key2144, -6), (key2145, -6)]

theorem rowCheck17326 : row17326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17326 := by decide +kernel

theorem rowEval17326 (x : Key → ℝ) : Integer.Sparse.eval row17326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17326, Integer.Sparse.eval_collectBalanced, rawRowCheck17326]

def rawRow17327 : Integer.Sparse Key := [(key2134, -1), (key2145, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2229, -1), (key2145, 2), (key2145, 2), (key2229, 2), (key2047, 1), (key2056, 1), (key2047, 1), (key2228, 1), (key2056, 1), (key2228, 1), (key2056, -2), (key2056, -2), (key2228, -2), (key2019, -1), (key2026, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2055, -1), (key2019, 1), (key2026, 1), (key2019, 1), (key2144, 1), (key2026, 1), (key2144, 1), (key2013, 2), (key2013, 2), (key2042, 2), (key2013, -2), (key2013, -2), (key2127, -2)]

theorem rawRowCheck17327 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form14 = rawRow17327 := by decide +kernel

def row17327 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

theorem rowCheck17327 : row17327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17327 := by decide +kernel

theorem rowEval17327 (x : Key → ℝ) : Integer.Sparse.eval row17327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck17327, Integer.Sparse.eval_collectBalanced, rawRowCheck17327]

def rawRow17328 : Integer.Sparse Key := [(key2145, -1), (key2134, -1), (key2229, -1), (key2134, -1), (key2229, -1), (key2145, -1), (key2145, 2), (key2229, 2), (key2145, 2), (key2056, 1), (key2047, 1), (key2228, 1), (key2047, 1), (key2228, 1), (key2056, 1), (key2056, -2), (key2228, -2), (key2056, -2), (key2026, -1), (key2019, -1), (key2055, -1), (key2019, -1), (key2055, -1), (key2026, -1), (key2026, 1), (key2019, 1), (key2144, 1), (key2019, 1), (key2144, 1), (key2026, 1), (key2013, 2), (key2042, 2), (key2013, 2), (key2013, -2), (key2127, -2), (key2013, -2)]

theorem rawRowCheck17328 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form14 = rawRow17328 := by decide +kernel

def row17328 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

theorem rowCheck17328 : row17328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17328 := by decide +kernel

theorem rowEval17328 (x : Key → ℝ) : Integer.Sparse.eval row17328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17328, Integer.Sparse.eval_collectBalanced, rawRowCheck17328]

def rawRow17329 : Integer.Sparse Key := [(key2229, -1), (key2229, -1), (key2145, -1), (key2145, -1), (key2134, -1), (key2134, -1), (key2229, 2), (key2145, 2), (key2145, 2), (key2228, 1), (key2228, 1), (key2056, 1), (key2056, 1), (key2047, 1), (key2047, 1), (key2228, -2), (key2056, -2), (key2056, -2), (key2055, -1), (key2055, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2144, 1), (key2144, 1), (key2026, 1), (key2026, 1), (key2019, 1), (key2019, 1), (key2042, 2), (key2013, 2), (key2013, 2), (key2127, -2), (key2013, -2), (key2013, -2)]

theorem rawRowCheck17329 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form14 = rawRow17329 := by decide +kernel

def row17329 : Integer.Sparse Key := [(key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2), (key2127, -2), (key2134, -2), (key2144, 2), (key2145, 2)]

theorem rowCheck17329 : row17329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17329 := by decide +kernel

theorem rowEval17329 (x : Key → ℝ) : Integer.Sparse.eval row17329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17329, Integer.Sparse.eval_collectBalanced, rawRowCheck17329]

def rawRow17330 : Integer.Sparse Key := [(key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2145, -1), (key2134, 2), (key2134, 2), (key2134, 2), (key2056, 1), (key2056, 1), (key2056, 1), (key2056, 1), (key2056, 1), (key2056, 1), (key2047, -2), (key2047, -2), (key2047, -2), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2144, -1), (key2055, 1), (key2055, 1), (key2055, 1), (key2055, 1), (key2055, 1), (key2055, 1), (key2127, 2), (key2127, 2), (key2127, 2), (key2042, -2), (key2042, -2), (key2042, -2)]

theorem rawRowCheck17330 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form14 = rawRow17330 := by decide +kernel

def row17330 : Integer.Sparse Key := [(key2042, -6), (key2047, -6), (key2055, 6), (key2056, 6), (key2127, 6), (key2134, 6), (key2144, -6), (key2145, -6)]

theorem rowCheck17330 : row17330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17330 := by decide +kernel

theorem rowEval17330 (x : Key → ℝ) : Integer.Sparse.eval row17330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck17330, Integer.Sparse.eval_collectBalanced, rawRowCheck17330]

def rawRow17331 : Integer.Sparse Key := [(key2014, -1), (key2018, -1), (key2043, -1), (key2046, -1), (key2051, -1), (key2052, -1), (key2023, 2), (key2051, 2), (key2052, 2), (key2014, 1), (key2018, 1), (key2128, 1), (key2133, 1), (key2138, 1), (key2141, 1), (key2023, -2), (key2138, -2), (key2141, -2), (key2014, -1), (key2018, -1), (key2043, -1), (key2046, -1), (key2051, -1), (key2052, -1), (key2014, 1), (key2018, 1), (key2128, 1), (key2133, 1), (key2138, 1), (key2141, 1), (key2023, 2), (key2051, 2), (key2052, 2), (key2023, -2), (key2138, -2), (key2141, -2)]

theorem rawRowCheck17331 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form15 = rawRow17331 := by decide +kernel

def row17331 : Integer.Sparse Key := [(key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2), (key2128, 2), (key2133, 2), (key2138, -2), (key2141, -2)]

theorem rowCheck17331 : row17331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17331 := by decide +kernel

theorem rowEval17331 (x : Key → ℝ) : Integer.Sparse.eval row17331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form15) x := by
  rw [rowCheck17331, Integer.Sparse.eval_collectBalanced, rawRowCheck17331]

def rawRow17332 : Integer.Sparse Key := [(key2018, -1), (key2014, -1), (key2046, -1), (key2043, -1), (key2052, -1), (key2051, -1), (key2023, 2), (key2052, 2), (key2051, 2), (key2018, 1), (key2014, 1), (key2133, 1), (key2128, 1), (key2141, 1), (key2138, 1), (key2023, -2), (key2141, -2), (key2138, -2), (key2018, -1), (key2014, -1), (key2046, -1), (key2043, -1), (key2052, -1), (key2051, -1), (key2018, 1), (key2014, 1), (key2133, 1), (key2128, 1), (key2141, 1), (key2138, 1), (key2023, 2), (key2052, 2), (key2051, 2), (key2023, -2), (key2141, -2), (key2138, -2)]

theorem rawRowCheck17332 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form15 = rawRow17332 := by decide +kernel

def row17332 : Integer.Sparse Key := [(key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2), (key2128, 2), (key2133, 2), (key2138, -2), (key2141, -2)]

theorem rowCheck17332 : row17332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17332 := by decide +kernel

theorem rowEval17332 (x : Key → ℝ) : Integer.Sparse.eval row17332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17332, Integer.Sparse.eval_collectBalanced, rawRowCheck17332]

def rawRow17333 : Integer.Sparse Key := [(key2043, -1), (key2051, -1), (key2014, -1), (key2052, -1), (key2018, -1), (key2046, -1), (key2051, 2), (key2023, 2), (key2052, 2), (key2128, 1), (key2138, 1), (key2014, 1), (key2141, 1), (key2018, 1), (key2133, 1), (key2138, -2), (key2023, -2), (key2141, -2), (key2043, -1), (key2051, -1), (key2014, -1), (key2052, -1), (key2018, -1), (key2046, -1), (key2128, 1), (key2138, 1), (key2014, 1), (key2141, 1), (key2018, 1), (key2133, 1), (key2051, 2), (key2023, 2), (key2052, 2), (key2138, -2), (key2023, -2), (key2141, -2)]

theorem rawRowCheck17333 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form15 = rawRow17333 := by decide +kernel

def row17333 : Integer.Sparse Key := [(key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2), (key2128, 2), (key2133, 2), (key2138, -2), (key2141, -2)]

theorem rowCheck17333 : row17333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17333 := by decide +kernel

theorem rowEval17333 (x : Key → ℝ) : Integer.Sparse.eval row17333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form15) x := by
  rw [rowCheck17333, Integer.Sparse.eval_collectBalanced, rawRowCheck17333]

def rawRow17334 : Integer.Sparse Key := [(key2051, -1), (key2043, -1), (key2052, -1), (key2014, -1), (key2046, -1), (key2018, -1), (key2051, 2), (key2052, 2), (key2023, 2), (key2138, 1), (key2128, 1), (key2141, 1), (key2014, 1), (key2133, 1), (key2018, 1), (key2138, -2), (key2141, -2), (key2023, -2), (key2051, -1), (key2043, -1), (key2052, -1), (key2014, -1), (key2046, -1), (key2018, -1), (key2138, 1), (key2128, 1), (key2141, 1), (key2014, 1), (key2133, 1), (key2018, 1), (key2051, 2), (key2052, 2), (key2023, 2), (key2138, -2), (key2141, -2), (key2023, -2)]

theorem rawRowCheck17334 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form15 = rawRow17334 := by decide +kernel

def row17334 : Integer.Sparse Key := [(key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2), (key2128, 2), (key2133, 2), (key2138, -2), (key2141, -2)]

theorem rowCheck17334 : row17334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17334 := by decide +kernel

theorem rowEval17334 (x : Key → ℝ) : Integer.Sparse.eval row17334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17334, Integer.Sparse.eval_collectBalanced, rawRowCheck17334]

def rawRow17335 : Integer.Sparse Key := [(key2046, -1), (key2052, -1), (key2018, -1), (key2051, -1), (key2014, -1), (key2043, -1), (key2052, 2), (key2023, 2), (key2051, 2), (key2133, 1), (key2141, 1), (key2018, 1), (key2138, 1), (key2014, 1), (key2128, 1), (key2141, -2), (key2023, -2), (key2138, -2), (key2046, -1), (key2052, -1), (key2018, -1), (key2051, -1), (key2014, -1), (key2043, -1), (key2133, 1), (key2141, 1), (key2018, 1), (key2138, 1), (key2014, 1), (key2128, 1), (key2052, 2), (key2023, 2), (key2051, 2), (key2141, -2), (key2023, -2), (key2138, -2)]

theorem rawRowCheck17335 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form15 = rawRow17335 := by decide +kernel

def row17335 : Integer.Sparse Key := [(key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2), (key2128, 2), (key2133, 2), (key2138, -2), (key2141, -2)]

theorem rowCheck17335 : row17335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17335 := by decide +kernel

theorem rowEval17335 (x : Key → ℝ) : Integer.Sparse.eval row17335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17335, Integer.Sparse.eval_collectBalanced, rawRowCheck17335]

def rawRow17336 : Integer.Sparse Key := [(key2052, -1), (key2046, -1), (key2051, -1), (key2018, -1), (key2043, -1), (key2014, -1), (key2052, 2), (key2051, 2), (key2023, 2), (key2141, 1), (key2133, 1), (key2138, 1), (key2018, 1), (key2128, 1), (key2014, 1), (key2141, -2), (key2138, -2), (key2023, -2), (key2052, -1), (key2046, -1), (key2051, -1), (key2018, -1), (key2043, -1), (key2014, -1), (key2141, 1), (key2133, 1), (key2138, 1), (key2018, 1), (key2128, 1), (key2014, 1), (key2052, 2), (key2051, 2), (key2023, 2), (key2141, -2), (key2138, -2), (key2023, -2)]

theorem rawRowCheck17336 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form15 = rawRow17336 := by decide +kernel

def row17336 : Integer.Sparse Key := [(key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2), (key2128, 2), (key2133, 2), (key2138, -2), (key2141, -2)]

theorem rowCheck17336 : row17336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17336 := by decide +kernel

theorem rowEval17336 (x : Key → ℝ) : Integer.Sparse.eval row17336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17336, Integer.Sparse.eval_collectBalanced, rawRowCheck17336]

def rawRow17337 : Integer.Sparse Key := [(key2014, -1), (key2023, -1), (key2014, -1), (key2052, -1), (key2023, -1), (key2052, -1), (key2018, 2), (key2018, 2), (key2046, 2), (key2014, 1), (key2023, 1), (key2014, 1), (key2141, 1), (key2023, 1), (key2141, 1), (key2018, -2), (key2018, -2), (key2133, -2), (key2128, -1), (key2138, -1), (key2128, -1), (key2221, -1), (key2138, -1), (key2221, -1), (key2043, 1), (key2051, 1), (key2043, 1), (key2222, 1), (key2051, 1), (key2222, 1), (key2138, 2), (key2138, 2), (key2221, 2), (key2051, -2), (key2051, -2), (key2222, -2)]

theorem rawRowCheck17337 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form15 = rawRow17337 := by decide +kernel

def row17337 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

theorem rowCheck17337 : row17337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17337 := by decide +kernel

theorem rowEval17337 (x : Key → ℝ) : Integer.Sparse.eval row17337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form15) x := by
  rw [rowCheck17337, Integer.Sparse.eval_collectBalanced, rawRowCheck17337]

def rawRow17338 : Integer.Sparse Key := [(key2023, -1), (key2014, -1), (key2052, -1), (key2014, -1), (key2052, -1), (key2023, -1), (key2018, 2), (key2046, 2), (key2018, 2), (key2023, 1), (key2014, 1), (key2141, 1), (key2014, 1), (key2141, 1), (key2023, 1), (key2018, -2), (key2133, -2), (key2018, -2), (key2138, -1), (key2128, -1), (key2221, -1), (key2128, -1), (key2221, -1), (key2138, -1), (key2051, 1), (key2043, 1), (key2222, 1), (key2043, 1), (key2222, 1), (key2051, 1), (key2138, 2), (key2221, 2), (key2138, 2), (key2051, -2), (key2222, -2), (key2051, -2)]

theorem rawRowCheck17338 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form15 = rawRow17338 := by decide +kernel

def row17338 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

theorem rowCheck17338 : row17338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17338 := by decide +kernel

theorem rowEval17338 (x : Key → ℝ) : Integer.Sparse.eval row17338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17338, Integer.Sparse.eval_collectBalanced, rawRowCheck17338]

def rawRow17339 : Integer.Sparse Key := [(key2052, -1), (key2052, -1), (key2023, -1), (key2023, -1), (key2014, -1), (key2014, -1), (key2046, 2), (key2018, 2), (key2018, 2), (key2141, 1), (key2141, 1), (key2023, 1), (key2023, 1), (key2014, 1), (key2014, 1), (key2133, -2), (key2018, -2), (key2018, -2), (key2221, -1), (key2221, -1), (key2138, -1), (key2138, -1), (key2128, -1), (key2128, -1), (key2222, 1), (key2222, 1), (key2051, 1), (key2051, 1), (key2043, 1), (key2043, 1), (key2221, 2), (key2138, 2), (key2138, 2), (key2222, -2), (key2051, -2), (key2051, -2)]

theorem rawRowCheck17339 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form15 = rawRow17339 := by decide +kernel

def row17339 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

theorem rowCheck17339 : row17339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17339 := by decide +kernel

theorem rowEval17339 (x : Key → ℝ) : Integer.Sparse.eval row17339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17339, Integer.Sparse.eval_collectBalanced, rawRowCheck17339]

def rawRow17340 : Integer.Sparse Key := [(key2018, -1), (key2023, -1), (key2018, -1), (key2051, -1), (key2023, -1), (key2051, -1), (key2014, 2), (key2014, 2), (key2043, 2), (key2018, 1), (key2023, 1), (key2018, 1), (key2138, 1), (key2023, 1), (key2138, 1), (key2014, -2), (key2014, -2), (key2128, -2), (key2133, -1), (key2141, -1), (key2133, -1), (key2222, -1), (key2141, -1), (key2222, -1), (key2046, 1), (key2052, 1), (key2046, 1), (key2221, 1), (key2052, 1), (key2221, 1), (key2141, 2), (key2141, 2), (key2222, 2), (key2052, -2), (key2052, -2), (key2221, -2)]

theorem rawRowCheck17340 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form15 = rawRow17340 := by decide +kernel

def row17340 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

theorem rowCheck17340 : row17340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17340 := by decide +kernel

theorem rowEval17340 (x : Key → ℝ) : Integer.Sparse.eval row17340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17340, Integer.Sparse.eval_collectBalanced, rawRowCheck17340]

def rawRow17341 : Integer.Sparse Key := [(key2023, -1), (key2018, -1), (key2051, -1), (key2018, -1), (key2051, -1), (key2023, -1), (key2014, 2), (key2043, 2), (key2014, 2), (key2023, 1), (key2018, 1), (key2138, 1), (key2018, 1), (key2138, 1), (key2023, 1), (key2014, -2), (key2128, -2), (key2014, -2), (key2141, -1), (key2133, -1), (key2222, -1), (key2133, -1), (key2222, -1), (key2141, -1), (key2052, 1), (key2046, 1), (key2221, 1), (key2046, 1), (key2221, 1), (key2052, 1), (key2141, 2), (key2222, 2), (key2141, 2), (key2052, -2), (key2221, -2), (key2052, -2)]

theorem rawRowCheck17341 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form15 = rawRow17341 := by decide +kernel

def row17341 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

theorem rowCheck17341 : row17341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17341 := by decide +kernel

theorem rowEval17341 (x : Key → ℝ) : Integer.Sparse.eval row17341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17341, Integer.Sparse.eval_collectBalanced, rawRowCheck17341]

def rawRow17342 : Integer.Sparse Key := [(key2051, -1), (key2051, -1), (key2023, -1), (key2023, -1), (key2018, -1), (key2018, -1), (key2043, 2), (key2014, 2), (key2014, 2), (key2138, 1), (key2138, 1), (key2023, 1), (key2023, 1), (key2018, 1), (key2018, 1), (key2128, -2), (key2014, -2), (key2014, -2), (key2222, -1), (key2222, -1), (key2141, -1), (key2141, -1), (key2133, -1), (key2133, -1), (key2221, 1), (key2221, 1), (key2052, 1), (key2052, 1), (key2046, 1), (key2046, 1), (key2222, 2), (key2141, 2), (key2141, 2), (key2221, -2), (key2052, -2), (key2052, -2)]

theorem rawRowCheck17342 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form15 = rawRow17342 := by decide +kernel

def row17342 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

theorem rowCheck17342 : row17342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17342 := by decide +kernel

theorem rowEval17342 (x : Key → ℝ) : Integer.Sparse.eval row17342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17342, Integer.Sparse.eval_collectBalanced, rawRowCheck17342]

def rawRow17343 : Integer.Sparse Key := [(key2128, -1), (key2138, -1), (key2128, -1), (key2221, -1), (key2138, -1), (key2221, -1), (key2138, 2), (key2138, 2), (key2221, 2), (key2043, 1), (key2051, 1), (key2043, 1), (key2222, 1), (key2051, 1), (key2222, 1), (key2051, -2), (key2051, -2), (key2222, -2), (key2014, -1), (key2023, -1), (key2014, -1), (key2052, -1), (key2023, -1), (key2052, -1), (key2014, 1), (key2023, 1), (key2014, 1), (key2141, 1), (key2023, 1), (key2141, 1), (key2018, 2), (key2018, 2), (key2046, 2), (key2018, -2), (key2018, -2), (key2133, -2)]

theorem rawRowCheck17343 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form15 = rawRow17343 := by decide +kernel

def row17343 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

theorem rowCheck17343 : row17343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17343 := by decide +kernel

theorem rowEval17343 (x : Key → ℝ) : Integer.Sparse.eval row17343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form15) x := by
  rw [rowCheck17343, Integer.Sparse.eval_collectBalanced, rawRowCheck17343]

def rawRow17344 : Integer.Sparse Key := [(key2138, -1), (key2128, -1), (key2221, -1), (key2128, -1), (key2221, -1), (key2138, -1), (key2138, 2), (key2221, 2), (key2138, 2), (key2051, 1), (key2043, 1), (key2222, 1), (key2043, 1), (key2222, 1), (key2051, 1), (key2051, -2), (key2222, -2), (key2051, -2), (key2023, -1), (key2014, -1), (key2052, -1), (key2014, -1), (key2052, -1), (key2023, -1), (key2023, 1), (key2014, 1), (key2141, 1), (key2014, 1), (key2141, 1), (key2023, 1), (key2018, 2), (key2046, 2), (key2018, 2), (key2018, -2), (key2133, -2), (key2018, -2)]

theorem rawRowCheck17344 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form15 = rawRow17344 := by decide +kernel

def row17344 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

theorem rowCheck17344 : row17344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17344 := by decide +kernel

theorem rowEval17344 (x : Key → ℝ) : Integer.Sparse.eval row17344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17344, Integer.Sparse.eval_collectBalanced, rawRowCheck17344]

def rawRow17345 : Integer.Sparse Key := [(key2221, -1), (key2221, -1), (key2138, -1), (key2138, -1), (key2128, -1), (key2128, -1), (key2221, 2), (key2138, 2), (key2138, 2), (key2222, 1), (key2222, 1), (key2051, 1), (key2051, 1), (key2043, 1), (key2043, 1), (key2222, -2), (key2051, -2), (key2051, -2), (key2052, -1), (key2052, -1), (key2023, -1), (key2023, -1), (key2014, -1), (key2014, -1), (key2141, 1), (key2141, 1), (key2023, 1), (key2023, 1), (key2014, 1), (key2014, 1), (key2046, 2), (key2018, 2), (key2018, 2), (key2133, -2), (key2018, -2), (key2018, -2)]

theorem rawRowCheck17345 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form15 = rawRow17345 := by decide +kernel

def row17345 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

theorem rowCheck17345 : row17345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17345 := by decide +kernel

theorem rowEval17345 (x : Key → ℝ) : Integer.Sparse.eval row17345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17345, Integer.Sparse.eval_collectBalanced, rawRowCheck17345]

def rawRow17346 : Integer.Sparse Key := [(key2138, -1), (key2138, -1), (key2138, -1), (key2138, -1), (key2138, -1), (key2138, -1), (key2128, 2), (key2128, 2), (key2128, 2), (key2051, 1), (key2051, 1), (key2051, 1), (key2051, 1), (key2051, 1), (key2051, 1), (key2043, -2), (key2043, -2), (key2043, -2), (key2141, -1), (key2141, -1), (key2141, -1), (key2141, -1), (key2141, -1), (key2141, -1), (key2052, 1), (key2052, 1), (key2052, 1), (key2052, 1), (key2052, 1), (key2052, 1), (key2133, 2), (key2133, 2), (key2133, 2), (key2046, -2), (key2046, -2), (key2046, -2)]

theorem rawRowCheck17346 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form15 = rawRow17346 := by decide +kernel

def row17346 : Integer.Sparse Key := [(key2043, -6), (key2046, -6), (key2051, 6), (key2052, 6), (key2128, 6), (key2133, 6), (key2138, -6), (key2141, -6)]

theorem rowCheck17346 : row17346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17346 := by decide +kernel

theorem rowEval17346 (x : Key → ℝ) : Integer.Sparse.eval row17346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17346, Integer.Sparse.eval_collectBalanced, rawRowCheck17346]

def rawRow17347 : Integer.Sparse Key := [(key2133, -1), (key2141, -1), (key2133, -1), (key2222, -1), (key2141, -1), (key2222, -1), (key2141, 2), (key2141, 2), (key2222, 2), (key2046, 1), (key2052, 1), (key2046, 1), (key2221, 1), (key2052, 1), (key2221, 1), (key2052, -2), (key2052, -2), (key2221, -2), (key2018, -1), (key2023, -1), (key2018, -1), (key2051, -1), (key2023, -1), (key2051, -1), (key2018, 1), (key2023, 1), (key2018, 1), (key2138, 1), (key2023, 1), (key2138, 1), (key2014, 2), (key2014, 2), (key2043, 2), (key2014, -2), (key2014, -2), (key2128, -2)]

theorem rawRowCheck17347 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form15 = rawRow17347 := by decide +kernel

def row17347 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

theorem rowCheck17347 : row17347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17347 := by decide +kernel

theorem rowEval17347 (x : Key → ℝ) : Integer.Sparse.eval row17347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck17347, Integer.Sparse.eval_collectBalanced, rawRowCheck17347]

def rawRow17348 : Integer.Sparse Key := [(key2141, -1), (key2133, -1), (key2222, -1), (key2133, -1), (key2222, -1), (key2141, -1), (key2141, 2), (key2222, 2), (key2141, 2), (key2052, 1), (key2046, 1), (key2221, 1), (key2046, 1), (key2221, 1), (key2052, 1), (key2052, -2), (key2221, -2), (key2052, -2), (key2023, -1), (key2018, -1), (key2051, -1), (key2018, -1), (key2051, -1), (key2023, -1), (key2023, 1), (key2018, 1), (key2138, 1), (key2018, 1), (key2138, 1), (key2023, 1), (key2014, 2), (key2043, 2), (key2014, 2), (key2014, -2), (key2128, -2), (key2014, -2)]

theorem rawRowCheck17348 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form15 = rawRow17348 := by decide +kernel

def row17348 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

theorem rowCheck17348 : row17348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17348 := by decide +kernel

theorem rowEval17348 (x : Key → ℝ) : Integer.Sparse.eval row17348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17348, Integer.Sparse.eval_collectBalanced, rawRowCheck17348]

def rawRow17349 : Integer.Sparse Key := [(key2222, -1), (key2222, -1), (key2141, -1), (key2141, -1), (key2133, -1), (key2133, -1), (key2222, 2), (key2141, 2), (key2141, 2), (key2221, 1), (key2221, 1), (key2052, 1), (key2052, 1), (key2046, 1), (key2046, 1), (key2221, -2), (key2052, -2), (key2052, -2), (key2051, -1), (key2051, -1), (key2023, -1), (key2023, -1), (key2018, -1), (key2018, -1), (key2138, 1), (key2138, 1), (key2023, 1), (key2023, 1), (key2018, 1), (key2018, 1), (key2043, 2), (key2014, 2), (key2014, 2), (key2128, -2), (key2014, -2), (key2014, -2)]

theorem rawRowCheck17349 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form15 = rawRow17349 := by decide +kernel

def row17349 : Integer.Sparse Key := [(key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2), (key2128, -2), (key2133, -2), (key2138, 2), (key2141, 2)]

theorem rowCheck17349 : row17349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17349 := by decide +kernel

theorem rowEval17349 (x : Key → ℝ) : Integer.Sparse.eval row17349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17349, Integer.Sparse.eval_collectBalanced, rawRowCheck17349]

def rawRow17350 : Integer.Sparse Key := [(key2141, -1), (key2141, -1), (key2141, -1), (key2141, -1), (key2141, -1), (key2141, -1), (key2133, 2), (key2133, 2), (key2133, 2), (key2052, 1), (key2052, 1), (key2052, 1), (key2052, 1), (key2052, 1), (key2052, 1), (key2046, -2), (key2046, -2), (key2046, -2), (key2138, -1), (key2138, -1), (key2138, -1), (key2138, -1), (key2138, -1), (key2138, -1), (key2051, 1), (key2051, 1), (key2051, 1), (key2051, 1), (key2051, 1), (key2051, 1), (key2128, 2), (key2128, 2), (key2128, 2), (key2043, -2), (key2043, -2), (key2043, -2)]

theorem rawRowCheck17350 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form15 = rawRow17350 := by decide +kernel

def row17350 : Integer.Sparse Key := [(key2043, -6), (key2046, -6), (key2051, 6), (key2052, 6), (key2128, 6), (key2133, 6), (key2138, -6), (key2141, -6)]

theorem rowCheck17350 : row17350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17350 := by decide +kernel

theorem rowEval17350 (x : Key → ℝ) : Integer.Sparse.eval row17350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck17350, Integer.Sparse.eval_collectBalanced, rawRowCheck17350]

def rawRow17351 : Integer.Sparse Key := [(key2017, 2), (key2137, 2), (key2142, 2), (key2022, -1), (key2024, -1), (key2137, -1), (key2142, -1), (key2172, -1), (key2173, -1), (key2017, 2), (key2137, 2), (key2142, 2), (key2050, -1), (key2053, -1), (key2137, -1), (key2142, -1), (key2264, -1), (key2265, -1), (key2022, -1), (key2024, -1), (key2137, -1), (key2142, -1), (key2172, -1), (key2173, -1), (key2050, -1), (key2053, -1), (key2137, -1), (key2142, -1), (key2264, -1), (key2265, -1), (key2075, 2), (key2076, 2), (key2172, 2), (key2173, 2), (key2264, 2), (key2265, 2)]

theorem rawRowCheck17351 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form16 = rawRow17351 := by decide +kernel

def row17351 : Integer.Sparse Key := [(key2017, 4), (key2022, -2), (key2024, -2), (key2050, -2), (key2053, -2), (key2075, 2), (key2076, 2)]

theorem rowCheck17351 : row17351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17351 := by decide +kernel

theorem rowEval17351 (x : Key → ℝ) : Integer.Sparse.eval row17351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form16) x := by
  rw [rowCheck17351, Integer.Sparse.eval_collectBalanced, rawRowCheck17351]

def rawRow17352 : Integer.Sparse Key := [(key2017, 2), (key2142, 2), (key2137, 2), (key2024, -1), (key2022, -1), (key2142, -1), (key2137, -1), (key2173, -1), (key2172, -1), (key2017, 2), (key2142, 2), (key2137, 2), (key2053, -1), (key2050, -1), (key2142, -1), (key2137, -1), (key2265, -1), (key2264, -1), (key2024, -1), (key2022, -1), (key2142, -1), (key2137, -1), (key2173, -1), (key2172, -1), (key2053, -1), (key2050, -1), (key2142, -1), (key2137, -1), (key2265, -1), (key2264, -1), (key2076, 2), (key2075, 2), (key2173, 2), (key2172, 2), (key2265, 2), (key2264, 2)]

theorem rawRowCheck17352 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form16 = rawRow17352 := by decide +kernel

def row17352 : Integer.Sparse Key := [(key2017, 4), (key2022, -2), (key2024, -2), (key2050, -2), (key2053, -2), (key2075, 2), (key2076, 2)]

theorem rowCheck17352 : row17352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17352 := by decide +kernel

theorem rowEval17352 (x : Key → ℝ) : Integer.Sparse.eval row17352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17352, Integer.Sparse.eval_collectBalanced, rawRowCheck17352]

def rawRow17353 : Integer.Sparse Key := [(key2137, 2), (key2017, 2), (key2142, 2), (key2137, -1), (key2172, -1), (key2022, -1), (key2173, -1), (key2024, -1), (key2142, -1), (key2137, 2), (key2017, 2), (key2142, 2), (key2137, -1), (key2264, -1), (key2050, -1), (key2265, -1), (key2053, -1), (key2142, -1), (key2137, -1), (key2172, -1), (key2022, -1), (key2173, -1), (key2024, -1), (key2142, -1), (key2137, -1), (key2264, -1), (key2050, -1), (key2265, -1), (key2053, -1), (key2142, -1), (key2172, 2), (key2264, 2), (key2075, 2), (key2265, 2), (key2076, 2), (key2173, 2)]

theorem rawRowCheck17353 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form16 = rawRow17353 := by decide +kernel

def row17353 : Integer.Sparse Key := [(key2017, 4), (key2022, -2), (key2024, -2), (key2050, -2), (key2053, -2), (key2075, 2), (key2076, 2)]

theorem rowCheck17353 : row17353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17353 := by decide +kernel

theorem rowEval17353 (x : Key → ℝ) : Integer.Sparse.eval row17353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form16) x := by
  rw [rowCheck17353, Integer.Sparse.eval_collectBalanced, rawRowCheck17353]

def rawRow17354 : Integer.Sparse Key := [(key2137, 2), (key2142, 2), (key2017, 2), (key2172, -1), (key2137, -1), (key2173, -1), (key2022, -1), (key2142, -1), (key2024, -1), (key2137, 2), (key2142, 2), (key2017, 2), (key2264, -1), (key2137, -1), (key2265, -1), (key2050, -1), (key2142, -1), (key2053, -1), (key2172, -1), (key2137, -1), (key2173, -1), (key2022, -1), (key2142, -1), (key2024, -1), (key2264, -1), (key2137, -1), (key2265, -1), (key2050, -1), (key2142, -1), (key2053, -1), (key2264, 2), (key2172, 2), (key2265, 2), (key2075, 2), (key2173, 2), (key2076, 2)]

theorem rawRowCheck17354 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form16 = rawRow17354 := by decide +kernel

def row17354 : Integer.Sparse Key := [(key2017, 4), (key2022, -2), (key2024, -2), (key2050, -2), (key2053, -2), (key2075, 2), (key2076, 2)]

theorem rowCheck17354 : row17354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17354 := by decide +kernel

theorem rowEval17354 (x : Key → ℝ) : Integer.Sparse.eval row17354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17354, Integer.Sparse.eval_collectBalanced, rawRowCheck17354]

def rawRow17355 : Integer.Sparse Key := [(key2142, 2), (key2017, 2), (key2137, 2), (key2142, -1), (key2173, -1), (key2024, -1), (key2172, -1), (key2022, -1), (key2137, -1), (key2142, 2), (key2017, 2), (key2137, 2), (key2142, -1), (key2265, -1), (key2053, -1), (key2264, -1), (key2050, -1), (key2137, -1), (key2142, -1), (key2173, -1), (key2024, -1), (key2172, -1), (key2022, -1), (key2137, -1), (key2142, -1), (key2265, -1), (key2053, -1), (key2264, -1), (key2050, -1), (key2137, -1), (key2173, 2), (key2265, 2), (key2076, 2), (key2264, 2), (key2075, 2), (key2172, 2)]

theorem rawRowCheck17355 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form16 = rawRow17355 := by decide +kernel

def row17355 : Integer.Sparse Key := [(key2017, 4), (key2022, -2), (key2024, -2), (key2050, -2), (key2053, -2), (key2075, 2), (key2076, 2)]

theorem rowCheck17355 : row17355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17355 := by decide +kernel

theorem rowEval17355 (x : Key → ℝ) : Integer.Sparse.eval row17355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17355, Integer.Sparse.eval_collectBalanced, rawRowCheck17355]

def rawRow17356 : Integer.Sparse Key := [(key2142, 2), (key2137, 2), (key2017, 2), (key2173, -1), (key2142, -1), (key2172, -1), (key2024, -1), (key2137, -1), (key2022, -1), (key2142, 2), (key2137, 2), (key2017, 2), (key2265, -1), (key2142, -1), (key2264, -1), (key2053, -1), (key2137, -1), (key2050, -1), (key2173, -1), (key2142, -1), (key2172, -1), (key2024, -1), (key2137, -1), (key2022, -1), (key2265, -1), (key2142, -1), (key2264, -1), (key2053, -1), (key2137, -1), (key2050, -1), (key2265, 2), (key2173, 2), (key2264, 2), (key2076, 2), (key2172, 2), (key2075, 2)]

theorem rawRowCheck17356 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form16 = rawRow17356 := by decide +kernel

def row17356 : Integer.Sparse Key := [(key2017, 4), (key2022, -2), (key2024, -2), (key2050, -2), (key2053, -2), (key2075, 2), (key2076, 2)]

theorem rowCheck17356 : row17356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17356 := by decide +kernel

theorem rowEval17356 (x : Key → ℝ) : Integer.Sparse.eval row17356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17356, Integer.Sparse.eval_collectBalanced, rawRowCheck17356]

def rawRow17357 : Integer.Sparse Key := [(key2022, 2), (key2022, 2), (key2173, 2), (key2017, -1), (key2024, -1), (key2017, -1), (key2142, -1), (key2024, -1), (key2142, -1), (key2050, 2), (key2050, 2), (key2265, 2), (key2017, -1), (key2053, -1), (key2017, -1), (key2142, -1), (key2053, -1), (key2142, -1), (key2050, -1), (key2075, -1), (key2050, -1), (key2265, -1), (key2075, -1), (key2265, -1), (key2022, -1), (key2076, -1), (key2022, -1), (key2173, -1), (key2076, -1), (key2173, -1), (key2024, 2), (key2053, 2), (key2024, 2), (key2142, 2), (key2053, 2), (key2142, 2)]

theorem rawRowCheck17357 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form16 = rawRow17357 := by decide +kernel

def row17357 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

theorem rowCheck17357 : row17357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17357 := by decide +kernel

theorem rowEval17357 (x : Key → ℝ) : Integer.Sparse.eval row17357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form16) x := by
  rw [rowCheck17357, Integer.Sparse.eval_collectBalanced, rawRowCheck17357]

def rawRow17358 : Integer.Sparse Key := [(key2022, 2), (key2173, 2), (key2022, 2), (key2024, -1), (key2017, -1), (key2142, -1), (key2017, -1), (key2142, -1), (key2024, -1), (key2050, 2), (key2265, 2), (key2050, 2), (key2053, -1), (key2017, -1), (key2142, -1), (key2017, -1), (key2142, -1), (key2053, -1), (key2075, -1), (key2050, -1), (key2265, -1), (key2050, -1), (key2265, -1), (key2075, -1), (key2076, -1), (key2022, -1), (key2173, -1), (key2022, -1), (key2173, -1), (key2076, -1), (key2053, 2), (key2024, 2), (key2142, 2), (key2024, 2), (key2142, 2), (key2053, 2)]

theorem rawRowCheck17358 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form16 = rawRow17358 := by decide +kernel

def row17358 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

theorem rowCheck17358 : row17358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17358 := by decide +kernel

theorem rowEval17358 (x : Key → ℝ) : Integer.Sparse.eval row17358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17358, Integer.Sparse.eval_collectBalanced, rawRowCheck17358]

def rawRow17359 : Integer.Sparse Key := [(key2173, 2), (key2022, 2), (key2022, 2), (key2142, -1), (key2142, -1), (key2024, -1), (key2024, -1), (key2017, -1), (key2017, -1), (key2265, 2), (key2050, 2), (key2050, 2), (key2142, -1), (key2142, -1), (key2053, -1), (key2053, -1), (key2017, -1), (key2017, -1), (key2265, -1), (key2265, -1), (key2075, -1), (key2075, -1), (key2050, -1), (key2050, -1), (key2173, -1), (key2173, -1), (key2076, -1), (key2076, -1), (key2022, -1), (key2022, -1), (key2142, 2), (key2142, 2), (key2053, 2), (key2053, 2), (key2024, 2), (key2024, 2)]

theorem rawRowCheck17359 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form16 = rawRow17359 := by decide +kernel

def row17359 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

theorem rowCheck17359 : row17359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17359 := by decide +kernel

theorem rowEval17359 (x : Key → ℝ) : Integer.Sparse.eval row17359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17359, Integer.Sparse.eval_collectBalanced, rawRowCheck17359]

def rawRow17360 : Integer.Sparse Key := [(key2024, 2), (key2024, 2), (key2172, 2), (key2017, -1), (key2022, -1), (key2017, -1), (key2137, -1), (key2022, -1), (key2137, -1), (key2053, 2), (key2053, 2), (key2264, 2), (key2017, -1), (key2050, -1), (key2017, -1), (key2137, -1), (key2050, -1), (key2137, -1), (key2053, -1), (key2076, -1), (key2053, -1), (key2264, -1), (key2076, -1), (key2264, -1), (key2024, -1), (key2075, -1), (key2024, -1), (key2172, -1), (key2075, -1), (key2172, -1), (key2022, 2), (key2050, 2), (key2022, 2), (key2137, 2), (key2050, 2), (key2137, 2)]

theorem rawRowCheck17360 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form16 = rawRow17360 := by decide +kernel

def row17360 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

theorem rowCheck17360 : row17360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17360 := by decide +kernel

theorem rowEval17360 (x : Key → ℝ) : Integer.Sparse.eval row17360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17360, Integer.Sparse.eval_collectBalanced, rawRowCheck17360]

def rawRow17361 : Integer.Sparse Key := [(key2024, 2), (key2172, 2), (key2024, 2), (key2022, -1), (key2017, -1), (key2137, -1), (key2017, -1), (key2137, -1), (key2022, -1), (key2053, 2), (key2264, 2), (key2053, 2), (key2050, -1), (key2017, -1), (key2137, -1), (key2017, -1), (key2137, -1), (key2050, -1), (key2076, -1), (key2053, -1), (key2264, -1), (key2053, -1), (key2264, -1), (key2076, -1), (key2075, -1), (key2024, -1), (key2172, -1), (key2024, -1), (key2172, -1), (key2075, -1), (key2050, 2), (key2022, 2), (key2137, 2), (key2022, 2), (key2137, 2), (key2050, 2)]

theorem rawRowCheck17361 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form16 = rawRow17361 := by decide +kernel

def row17361 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

theorem rowCheck17361 : row17361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17361 := by decide +kernel

theorem rowEval17361 (x : Key → ℝ) : Integer.Sparse.eval row17361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17361, Integer.Sparse.eval_collectBalanced, rawRowCheck17361]

def rawRow17362 : Integer.Sparse Key := [(key2172, 2), (key2024, 2), (key2024, 2), (key2137, -1), (key2137, -1), (key2022, -1), (key2022, -1), (key2017, -1), (key2017, -1), (key2264, 2), (key2053, 2), (key2053, 2), (key2137, -1), (key2137, -1), (key2050, -1), (key2050, -1), (key2017, -1), (key2017, -1), (key2264, -1), (key2264, -1), (key2076, -1), (key2076, -1), (key2053, -1), (key2053, -1), (key2172, -1), (key2172, -1), (key2075, -1), (key2075, -1), (key2024, -1), (key2024, -1), (key2137, 2), (key2137, 2), (key2050, 2), (key2050, 2), (key2022, 2), (key2022, 2)]

theorem rawRowCheck17362 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form16 = rawRow17362 := by decide +kernel

def row17362 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

theorem rowCheck17362 : row17362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17362 := by decide +kernel

theorem rowEval17362 (x : Key → ℝ) : Integer.Sparse.eval row17362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17362, Integer.Sparse.eval_collectBalanced, rawRowCheck17362]

def rawRow17363 : Integer.Sparse Key := [(key2050, 2), (key2050, 2), (key2265, 2), (key2050, -1), (key2075, -1), (key2050, -1), (key2265, -1), (key2075, -1), (key2265, -1), (key2022, 2), (key2022, 2), (key2173, 2), (key2022, -1), (key2076, -1), (key2022, -1), (key2173, -1), (key2076, -1), (key2173, -1), (key2017, -1), (key2024, -1), (key2017, -1), (key2142, -1), (key2024, -1), (key2142, -1), (key2017, -1), (key2053, -1), (key2017, -1), (key2142, -1), (key2053, -1), (key2142, -1), (key2024, 2), (key2053, 2), (key2024, 2), (key2142, 2), (key2053, 2), (key2142, 2)]

theorem rawRowCheck17363 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form16 = rawRow17363 := by decide +kernel

def row17363 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

theorem rowCheck17363 : row17363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17363 := by decide +kernel

theorem rowEval17363 (x : Key → ℝ) : Integer.Sparse.eval row17363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form16) x := by
  rw [rowCheck17363, Integer.Sparse.eval_collectBalanced, rawRowCheck17363]

def rawRow17364 : Integer.Sparse Key := [(key2050, 2), (key2265, 2), (key2050, 2), (key2075, -1), (key2050, -1), (key2265, -1), (key2050, -1), (key2265, -1), (key2075, -1), (key2022, 2), (key2173, 2), (key2022, 2), (key2076, -1), (key2022, -1), (key2173, -1), (key2022, -1), (key2173, -1), (key2076, -1), (key2024, -1), (key2017, -1), (key2142, -1), (key2017, -1), (key2142, -1), (key2024, -1), (key2053, -1), (key2017, -1), (key2142, -1), (key2017, -1), (key2142, -1), (key2053, -1), (key2053, 2), (key2024, 2), (key2142, 2), (key2024, 2), (key2142, 2), (key2053, 2)]

theorem rawRowCheck17364 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form16 = rawRow17364 := by decide +kernel

def row17364 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

theorem rowCheck17364 : row17364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17364 := by decide +kernel

theorem rowEval17364 (x : Key → ℝ) : Integer.Sparse.eval row17364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17364, Integer.Sparse.eval_collectBalanced, rawRowCheck17364]

def rawRow17365 : Integer.Sparse Key := [(key2265, 2), (key2050, 2), (key2050, 2), (key2265, -1), (key2265, -1), (key2075, -1), (key2075, -1), (key2050, -1), (key2050, -1), (key2173, 2), (key2022, 2), (key2022, 2), (key2173, -1), (key2173, -1), (key2076, -1), (key2076, -1), (key2022, -1), (key2022, -1), (key2142, -1), (key2142, -1), (key2024, -1), (key2024, -1), (key2017, -1), (key2017, -1), (key2142, -1), (key2142, -1), (key2053, -1), (key2053, -1), (key2017, -1), (key2017, -1), (key2142, 2), (key2142, 2), (key2053, 2), (key2053, 2), (key2024, 2), (key2024, 2)]

theorem rawRowCheck17365 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form16 = rawRow17365 := by decide +kernel

def row17365 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

theorem rowCheck17365 : row17365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17365 := by decide +kernel

theorem rowEval17365 (x : Key → ℝ) : Integer.Sparse.eval row17365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17365, Integer.Sparse.eval_collectBalanced, rawRowCheck17365]

def rawRow17366 : Integer.Sparse Key := [(key2075, 2), (key2075, 2), (key2075, 2), (key2050, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2076, 2), (key2076, 2), (key2076, 2), (key2022, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2017, 2), (key2017, 2), (key2017, 2), (key2017, 2), (key2017, 2), (key2017, 2)]

theorem rawRowCheck17366 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form16 = rawRow17366 := by decide +kernel

def row17366 : Integer.Sparse Key := [(key2017, 12), (key2022, -6), (key2024, -6), (key2050, -6), (key2053, -6), (key2075, 6), (key2076, 6)]

theorem rowCheck17366 : row17366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17366 := by decide +kernel

theorem rowEval17366 (x : Key → ℝ) : Integer.Sparse.eval row17366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17366, Integer.Sparse.eval_collectBalanced, rawRowCheck17366]

def rawRow17367 : Integer.Sparse Key := [(key2053, 2), (key2053, 2), (key2264, 2), (key2053, -1), (key2076, -1), (key2053, -1), (key2264, -1), (key2076, -1), (key2264, -1), (key2024, 2), (key2024, 2), (key2172, 2), (key2024, -1), (key2075, -1), (key2024, -1), (key2172, -1), (key2075, -1), (key2172, -1), (key2017, -1), (key2022, -1), (key2017, -1), (key2137, -1), (key2022, -1), (key2137, -1), (key2017, -1), (key2050, -1), (key2017, -1), (key2137, -1), (key2050, -1), (key2137, -1), (key2022, 2), (key2050, 2), (key2022, 2), (key2137, 2), (key2050, 2), (key2137, 2)]

theorem rawRowCheck17367 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form16 = rawRow17367 := by decide +kernel

def row17367 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

theorem rowCheck17367 : row17367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17367 := by decide +kernel

theorem rowEval17367 (x : Key → ℝ) : Integer.Sparse.eval row17367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck17367, Integer.Sparse.eval_collectBalanced, rawRowCheck17367]

def rawRow17368 : Integer.Sparse Key := [(key2053, 2), (key2264, 2), (key2053, 2), (key2076, -1), (key2053, -1), (key2264, -1), (key2053, -1), (key2264, -1), (key2076, -1), (key2024, 2), (key2172, 2), (key2024, 2), (key2075, -1), (key2024, -1), (key2172, -1), (key2024, -1), (key2172, -1), (key2075, -1), (key2022, -1), (key2017, -1), (key2137, -1), (key2017, -1), (key2137, -1), (key2022, -1), (key2050, -1), (key2017, -1), (key2137, -1), (key2017, -1), (key2137, -1), (key2050, -1), (key2050, 2), (key2022, 2), (key2137, 2), (key2022, 2), (key2137, 2), (key2050, 2)]

theorem rawRowCheck17368 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form16 = rawRow17368 := by decide +kernel

def row17368 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

theorem rowCheck17368 : row17368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17368 := by decide +kernel

theorem rowEval17368 (x : Key → ℝ) : Integer.Sparse.eval row17368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17368, Integer.Sparse.eval_collectBalanced, rawRowCheck17368]

def rawRow17369 : Integer.Sparse Key := [(key2264, 2), (key2053, 2), (key2053, 2), (key2264, -1), (key2264, -1), (key2076, -1), (key2076, -1), (key2053, -1), (key2053, -1), (key2172, 2), (key2024, 2), (key2024, 2), (key2172, -1), (key2172, -1), (key2075, -1), (key2075, -1), (key2024, -1), (key2024, -1), (key2137, -1), (key2137, -1), (key2022, -1), (key2022, -1), (key2017, -1), (key2017, -1), (key2137, -1), (key2137, -1), (key2050, -1), (key2050, -1), (key2017, -1), (key2017, -1), (key2137, 2), (key2137, 2), (key2050, 2), (key2050, 2), (key2022, 2), (key2022, 2)]

theorem rawRowCheck17369 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form16 = rawRow17369 := by decide +kernel

def row17369 : Integer.Sparse Key := [(key2017, -4), (key2022, 2), (key2024, 2), (key2050, 2), (key2053, 2), (key2075, -2), (key2076, -2)]

theorem rowCheck17369 : row17369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17369 := by decide +kernel

theorem rowEval17369 (x : Key → ℝ) : Integer.Sparse.eval row17369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17369, Integer.Sparse.eval_collectBalanced, rawRowCheck17369]

def rawRow17370 : Integer.Sparse Key := [(key2076, 2), (key2076, 2), (key2076, 2), (key2053, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2053, -1), (key2075, 2), (key2075, 2), (key2075, 2), (key2024, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2024, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2050, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2022, -1), (key2017, 2), (key2017, 2), (key2017, 2), (key2017, 2), (key2017, 2), (key2017, 2)]

theorem rawRowCheck17370 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form16 = rawRow17370 := by decide +kernel

def row17370 : Integer.Sparse Key := [(key2017, 12), (key2022, -6), (key2024, -6), (key2050, -6), (key2053, -6), (key2075, 6), (key2076, 6)]

theorem rowCheck17370 : row17370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17370 := by decide +kernel

theorem rowEval17370 (x : Key → ℝ) : Integer.Sparse.eval row17370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck17370, Integer.Sparse.eval_collectBalanced, rawRowCheck17370]

def rawRow17371 : Integer.Sparse Key := [(key770, 4), (key774, 4), (key783, 4), (key770, -2), (key774, -2), (key797, -2), (key834, -2), (key808, -2), (key837, -2), (key770, -2), (key774, -2), (key797, -2), (key834, -2), (key808, -2), (key837, -2), (key797, 4), (key834, 4), (key932, 4)]

theorem rawRowCheck17371 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form17 = rawRow17371 := by decide +kernel

def row17371 : Integer.Sparse Key := [(key783, 4), (key808, -4), (key837, -4), (key932, 4)]

theorem rowCheck17371 : row17371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17371 := by decide +kernel

theorem rowEval17371 (x : Key → ℝ) : Integer.Sparse.eval row17371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form17) x := by
  rw [rowCheck17371, Integer.Sparse.eval_collectBalanced, rawRowCheck17371]

def rawRow17372 : Integer.Sparse Key := [(key774, 4), (key770, 4), (key783, 4), (key774, -2), (key770, -2), (key834, -2), (key797, -2), (key837, -2), (key808, -2), (key774, -2), (key770, -2), (key834, -2), (key797, -2), (key837, -2), (key808, -2), (key834, 4), (key797, 4), (key932, 4)]

theorem rawRowCheck17372 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form17 = rawRow17372 := by decide +kernel

def row17372 : Integer.Sparse Key := [(key783, 4), (key808, -4), (key837, -4), (key932, 4)]

theorem rowCheck17372 : row17372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17372 := by decide +kernel

theorem rowEval17372 (x : Key → ℝ) : Integer.Sparse.eval row17372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17372, Integer.Sparse.eval_collectBalanced, rawRowCheck17372]

def rawRow17373 : Integer.Sparse Key := [(key770, 4), (key783, 4), (key774, 4), (key797, -2), (key808, -2), (key770, -2), (key837, -2), (key774, -2), (key834, -2), (key797, -2), (key808, -2), (key770, -2), (key837, -2), (key774, -2), (key834, -2), (key797, 4), (key932, 4), (key834, 4)]

theorem rawRowCheck17373 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form17 = rawRow17373 := by decide +kernel

def row17373 : Integer.Sparse Key := [(key783, 4), (key808, -4), (key837, -4), (key932, 4)]

theorem rowCheck17373 : row17373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17373 := by decide +kernel

theorem rowEval17373 (x : Key → ℝ) : Integer.Sparse.eval row17373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form17) x := by
  rw [rowCheck17373, Integer.Sparse.eval_collectBalanced, rawRowCheck17373]

def rawRow17374 : Integer.Sparse Key := [(key783, 4), (key770, 4), (key774, 4), (key808, -2), (key797, -2), (key837, -2), (key770, -2), (key834, -2), (key774, -2), (key808, -2), (key797, -2), (key837, -2), (key770, -2), (key834, -2), (key774, -2), (key932, 4), (key797, 4), (key834, 4)]

theorem rawRowCheck17374 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form17 = rawRow17374 := by decide +kernel

def row17374 : Integer.Sparse Key := [(key783, 4), (key808, -4), (key837, -4), (key932, 4)]

theorem rowCheck17374 : row17374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17374 := by decide +kernel

theorem rowEval17374 (x : Key → ℝ) : Integer.Sparse.eval row17374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17374, Integer.Sparse.eval_collectBalanced, rawRowCheck17374]

def rawRow17375 : Integer.Sparse Key := [(key774, 4), (key783, 4), (key770, 4), (key834, -2), (key837, -2), (key774, -2), (key808, -2), (key770, -2), (key797, -2), (key834, -2), (key837, -2), (key774, -2), (key808, -2), (key770, -2), (key797, -2), (key834, 4), (key932, 4), (key797, 4)]

theorem rawRowCheck17375 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form17 = rawRow17375 := by decide +kernel

def row17375 : Integer.Sparse Key := [(key783, 4), (key808, -4), (key837, -4), (key932, 4)]

theorem rowCheck17375 : row17375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17375 := by decide +kernel

theorem rowEval17375 (x : Key → ℝ) : Integer.Sparse.eval row17375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17375, Integer.Sparse.eval_collectBalanced, rawRowCheck17375]

def rawRow17376 : Integer.Sparse Key := [(key783, 4), (key774, 4), (key770, 4), (key837, -2), (key834, -2), (key808, -2), (key774, -2), (key797, -2), (key770, -2), (key837, -2), (key834, -2), (key808, -2), (key774, -2), (key797, -2), (key770, -2), (key932, 4), (key834, 4), (key797, 4)]

theorem rawRowCheck17376 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form17 = rawRow17376 := by decide +kernel

def row17376 : Integer.Sparse Key := [(key783, 4), (key808, -4), (key837, -4), (key932, 4)]

theorem rowCheck17376 : row17376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17376 := by decide +kernel

theorem rowEval17376 (x : Key → ℝ) : Integer.Sparse.eval row17376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17376, Integer.Sparse.eval_collectBalanced, rawRowCheck17376]

def rawRow17377 : Integer.Sparse Key := [(key797, 4), (key808, 4), (key808, 4), (key770, -2), (key783, -2), (key770, -2), (key837, -2), (key783, -2), (key837, -2), (key797, -2), (key808, -2), (key797, -2), (key932, -2), (key808, -2), (key932, -2), (key770, 4), (key837, 4), (key837, 4)]

theorem rawRowCheck17377 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form17 = rawRow17377 := by decide +kernel

def row17377 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

theorem rowCheck17377 : row17377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17377 := by decide +kernel

theorem rowEval17377 (x : Key → ℝ) : Integer.Sparse.eval row17377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form17) x := by
  rw [rowCheck17377, Integer.Sparse.eval_collectBalanced, rawRowCheck17377]

def rawRow17378 : Integer.Sparse Key := [(key808, 4), (key797, 4), (key808, 4), (key783, -2), (key770, -2), (key837, -2), (key770, -2), (key837, -2), (key783, -2), (key808, -2), (key797, -2), (key932, -2), (key797, -2), (key932, -2), (key808, -2), (key837, 4), (key770, 4), (key837, 4)]

theorem rawRowCheck17378 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form17 = rawRow17378 := by decide +kernel

def row17378 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

theorem rowCheck17378 : row17378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17378 := by decide +kernel

theorem rowEval17378 (x : Key → ℝ) : Integer.Sparse.eval row17378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17378, Integer.Sparse.eval_collectBalanced, rawRowCheck17378]

def rawRow17379 : Integer.Sparse Key := [(key808, 4), (key808, 4), (key797, 4), (key837, -2), (key837, -2), (key783, -2), (key783, -2), (key770, -2), (key770, -2), (key932, -2), (key932, -2), (key808, -2), (key808, -2), (key797, -2), (key797, -2), (key837, 4), (key837, 4), (key770, 4)]

theorem rawRowCheck17379 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form17 = rawRow17379 := by decide +kernel

def row17379 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

theorem rowCheck17379 : row17379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17379 := by decide +kernel

theorem rowEval17379 (x : Key → ℝ) : Integer.Sparse.eval row17379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17379, Integer.Sparse.eval_collectBalanced, rawRowCheck17379]

def rawRow17380 : Integer.Sparse Key := [(key834, 4), (key837, 4), (key837, 4), (key774, -2), (key783, -2), (key774, -2), (key808, -2), (key783, -2), (key808, -2), (key834, -2), (key837, -2), (key834, -2), (key932, -2), (key837, -2), (key932, -2), (key774, 4), (key808, 4), (key808, 4)]

theorem rawRowCheck17380 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form17 = rawRow17380 := by decide +kernel

def row17380 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

theorem rowCheck17380 : row17380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17380 := by decide +kernel

theorem rowEval17380 (x : Key → ℝ) : Integer.Sparse.eval row17380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17380, Integer.Sparse.eval_collectBalanced, rawRowCheck17380]

def rawRow17381 : Integer.Sparse Key := [(key837, 4), (key834, 4), (key837, 4), (key783, -2), (key774, -2), (key808, -2), (key774, -2), (key808, -2), (key783, -2), (key837, -2), (key834, -2), (key932, -2), (key834, -2), (key932, -2), (key837, -2), (key808, 4), (key774, 4), (key808, 4)]

theorem rawRowCheck17381 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form17 = rawRow17381 := by decide +kernel

def row17381 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

theorem rowCheck17381 : row17381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17381 := by decide +kernel

theorem rowEval17381 (x : Key → ℝ) : Integer.Sparse.eval row17381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17381, Integer.Sparse.eval_collectBalanced, rawRowCheck17381]

def rawRow17382 : Integer.Sparse Key := [(key837, 4), (key837, 4), (key834, 4), (key808, -2), (key808, -2), (key783, -2), (key783, -2), (key774, -2), (key774, -2), (key932, -2), (key932, -2), (key837, -2), (key837, -2), (key834, -2), (key834, -2), (key808, 4), (key808, 4), (key774, 4)]

theorem rawRowCheck17382 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form17 = rawRow17382 := by decide +kernel

def row17382 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

theorem rowCheck17382 : row17382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17382 := by decide +kernel

theorem rowEval17382 (x : Key → ℝ) : Integer.Sparse.eval row17382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17382, Integer.Sparse.eval_collectBalanced, rawRowCheck17382]

def rawRow17383 : Integer.Sparse Key := [(key797, 4), (key808, 4), (key808, 4), (key797, -2), (key808, -2), (key797, -2), (key932, -2), (key808, -2), (key932, -2), (key770, -2), (key783, -2), (key770, -2), (key837, -2), (key783, -2), (key837, -2), (key770, 4), (key837, 4), (key837, 4)]

theorem rawRowCheck17383 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form17 = rawRow17383 := by decide +kernel

def row17383 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

theorem rowCheck17383 : row17383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17383 := by decide +kernel

theorem rowEval17383 (x : Key → ℝ) : Integer.Sparse.eval row17383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form17) x := by
  rw [rowCheck17383, Integer.Sparse.eval_collectBalanced, rawRowCheck17383]

def rawRow17384 : Integer.Sparse Key := [(key808, 4), (key797, 4), (key808, 4), (key808, -2), (key797, -2), (key932, -2), (key797, -2), (key932, -2), (key808, -2), (key783, -2), (key770, -2), (key837, -2), (key770, -2), (key837, -2), (key783, -2), (key837, 4), (key770, 4), (key837, 4)]

theorem rawRowCheck17384 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form17 = rawRow17384 := by decide +kernel

def row17384 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

theorem rowCheck17384 : row17384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17384 := by decide +kernel

theorem rowEval17384 (x : Key → ℝ) : Integer.Sparse.eval row17384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17384, Integer.Sparse.eval_collectBalanced, rawRowCheck17384]

def rawRow17385 : Integer.Sparse Key := [(key808, 4), (key808, 4), (key797, 4), (key932, -2), (key932, -2), (key808, -2), (key808, -2), (key797, -2), (key797, -2), (key837, -2), (key837, -2), (key783, -2), (key783, -2), (key770, -2), (key770, -2), (key837, 4), (key837, 4), (key770, 4)]

theorem rawRowCheck17385 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form17 = rawRow17385 := by decide +kernel

def row17385 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

theorem rowCheck17385 : row17385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17385 := by decide +kernel

theorem rowEval17385 (x : Key → ℝ) : Integer.Sparse.eval row17385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17385, Integer.Sparse.eval_collectBalanced, rawRowCheck17385]

def rawRow17386 : Integer.Sparse Key := [(key932, 4), (key932, 4), (key932, 4), (key808, -2), (key808, -2), (key808, -2), (key808, -2), (key808, -2), (key808, -2), (key837, -2), (key837, -2), (key837, -2), (key837, -2), (key837, -2), (key837, -2), (key783, 4), (key783, 4), (key783, 4)]

theorem rawRowCheck17386 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form17 = rawRow17386 := by decide +kernel

def row17386 : Integer.Sparse Key := [(key783, 12), (key808, -12), (key837, -12), (key932, 12)]

theorem rowCheck17386 : row17386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17386 := by decide +kernel

theorem rowEval17386 (x : Key → ℝ) : Integer.Sparse.eval row17386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17386, Integer.Sparse.eval_collectBalanced, rawRowCheck17386]

def rawRow17387 : Integer.Sparse Key := [(key834, 4), (key837, 4), (key837, 4), (key834, -2), (key837, -2), (key834, -2), (key932, -2), (key837, -2), (key932, -2), (key774, -2), (key783, -2), (key774, -2), (key808, -2), (key783, -2), (key808, -2), (key774, 4), (key808, 4), (key808, 4)]

theorem rawRowCheck17387 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form17 = rawRow17387 := by decide +kernel

def row17387 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

theorem rowCheck17387 : row17387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17387 := by decide +kernel

theorem rowEval17387 (x : Key → ℝ) : Integer.Sparse.eval row17387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck17387, Integer.Sparse.eval_collectBalanced, rawRowCheck17387]

def rawRow17388 : Integer.Sparse Key := [(key837, 4), (key834, 4), (key837, 4), (key837, -2), (key834, -2), (key932, -2), (key834, -2), (key932, -2), (key837, -2), (key783, -2), (key774, -2), (key808, -2), (key774, -2), (key808, -2), (key783, -2), (key808, 4), (key774, 4), (key808, 4)]

theorem rawRowCheck17388 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form17 = rawRow17388 := by decide +kernel

def row17388 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

theorem rowCheck17388 : row17388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17388 := by decide +kernel

theorem rowEval17388 (x : Key → ℝ) : Integer.Sparse.eval row17388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17388, Integer.Sparse.eval_collectBalanced, rawRowCheck17388]

def rawRow17389 : Integer.Sparse Key := [(key837, 4), (key837, 4), (key834, 4), (key932, -2), (key932, -2), (key837, -2), (key837, -2), (key834, -2), (key834, -2), (key808, -2), (key808, -2), (key783, -2), (key783, -2), (key774, -2), (key774, -2), (key808, 4), (key808, 4), (key774, 4)]

theorem rawRowCheck17389 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form17 = rawRow17389 := by decide +kernel

def row17389 : Integer.Sparse Key := [(key783, -4), (key808, 4), (key837, 4), (key932, -4)]

theorem rowCheck17389 : row17389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17389 := by decide +kernel

theorem rowEval17389 (x : Key → ℝ) : Integer.Sparse.eval row17389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17389, Integer.Sparse.eval_collectBalanced, rawRowCheck17389]

def rawRow17390 : Integer.Sparse Key := [(key932, 4), (key932, 4), (key932, 4), (key837, -2), (key837, -2), (key837, -2), (key837, -2), (key837, -2), (key837, -2), (key808, -2), (key808, -2), (key808, -2), (key808, -2), (key808, -2), (key808, -2), (key783, 4), (key783, 4), (key783, 4)]

theorem rawRowCheck17390 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form17 = rawRow17390 := by decide +kernel

def row17390 : Integer.Sparse Key := [(key783, 12), (key808, -12), (key837, -12), (key932, 12)]

theorem rowCheck17390 : row17390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17390 := by decide +kernel

theorem rowEval17390 (x : Key → ℝ) : Integer.Sparse.eval row17390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck17390, Integer.Sparse.eval_collectBalanced, rawRowCheck17390]

def rawRow17391 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, -2), (key766, -2), (key768, -2), (key769, -2), (key761, 2), (key766, 2), (key793, 2), (key768, 2), (key769, 2), (key793, 2), (key761, 2), (key766, 2), (key793, 2), (key793, -6), (key768, 2), (key769, 2), (key793, 2), (key793, -6)]

theorem rawRowCheck17391 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form18 = rawRow17391 := by decide +kernel

def row17391 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, 2), (key766, 2), (key768, 2), (key769, 2), (key793, -4)]

theorem rowCheck17391 : row17391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17391 := by decide +kernel

theorem rowEval17391 (x : Key → ℝ) : Integer.Sparse.eval row17391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form18) x := by
  rw [rowCheck17391, Integer.Sparse.eval_collectBalanced, rawRowCheck17391]

def rawRow17392 : Integer.Sparse Key := [(key759, -2), (key757, -2), (key766, -2), (key761, -2), (key769, -2), (key768, -2), (key766, 2), (key761, 2), (key793, 2), (key769, 2), (key768, 2), (key793, 2), (key766, 2), (key761, 2), (key793, 2), (key793, -6), (key769, 2), (key768, 2), (key793, 2), (key793, -6)]

theorem rawRowCheck17392 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form18 = rawRow17392 := by decide +kernel

def row17392 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, 2), (key766, 2), (key768, 2), (key769, 2), (key793, -4)]

theorem rowCheck17392 : row17392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17392 := by decide +kernel

theorem rowEval17392 (x : Key → ℝ) : Integer.Sparse.eval row17392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17392, Integer.Sparse.eval_collectBalanced, rawRowCheck17392]

def rawRow17393 : Integer.Sparse Key := [(key761, -2), (key766, -2), (key757, -2), (key769, -2), (key759, -2), (key766, -2), (key761, 2), (key793, 2), (key766, 2), (key768, 2), (key793, 2), (key769, 2), (key761, 2), (key793, 2), (key766, 2), (key793, -6), (key768, 2), (key793, 2), (key769, 2), (key793, -6)]

theorem rawRowCheck17393 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form18 = rawRow17393 := by decide +kernel

def row17393 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, 2), (key768, 4), (key769, 2), (key793, -4)]

theorem rowCheck17393 : row17393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17393 := by decide +kernel

theorem rowEval17393 (x : Key → ℝ) : Integer.Sparse.eval row17393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form18) x := by
  rw [rowCheck17393, Integer.Sparse.eval_collectBalanced, rawRowCheck17393]

def rawRow17394 : Integer.Sparse Key := [(key766, -2), (key761, -2), (key769, -2), (key757, -2), (key766, -2), (key759, -2), (key793, 2), (key761, 2), (key766, 2), (key793, 2), (key768, 2), (key769, 2), (key793, 2), (key761, 2), (key766, 2), (key793, -6), (key793, 2), (key768, 2), (key769, 2), (key793, -6)]

theorem rawRowCheck17394 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form18 = rawRow17394 := by decide +kernel

def row17394 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, 2), (key768, 4), (key769, 2), (key793, -4)]

theorem rowCheck17394 : row17394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17394 := by decide +kernel

theorem rowEval17394 (x : Key → ℝ) : Integer.Sparse.eval row17394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17394, Integer.Sparse.eval_collectBalanced, rawRowCheck17394]

def rawRow17395 : Integer.Sparse Key := [(key768, -2), (key769, -2), (key759, -2), (key766, -2), (key757, -2), (key761, -2), (key766, 2), (key793, 2), (key761, 2), (key769, 2), (key793, 2), (key768, 2), (key766, 2), (key793, 2), (key761, 2), (key793, -6), (key769, 2), (key793, 2), (key768, 2), (key793, -6)]

theorem rawRowCheck17395 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form18 = rawRow17395 := by decide +kernel

def row17395 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, 2), (key766, 2), (key768, 2), (key769, 2), (key793, -4)]

theorem rowCheck17395 : row17395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17395 := by decide +kernel

theorem rowEval17395 (x : Key → ℝ) : Integer.Sparse.eval row17395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17395, Integer.Sparse.eval_collectBalanced, rawRowCheck17395]

def rawRow17396 : Integer.Sparse Key := [(key769, -2), (key768, -2), (key766, -2), (key759, -2), (key761, -2), (key757, -2), (key793, 2), (key766, 2), (key761, 2), (key793, 2), (key769, 2), (key768, 2), (key793, 2), (key766, 2), (key761, 2), (key793, -6), (key793, 2), (key769, 2), (key768, 2), (key793, -6)]

theorem rawRowCheck17396 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form18 = rawRow17396 := by decide +kernel

def row17396 : Integer.Sparse Key := [(key757, -2), (key759, -2), (key761, 2), (key766, 2), (key768, 2), (key769, 2), (key793, -4)]

theorem rowCheck17396 : row17396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17396 := by decide +kernel

theorem rowEval17396 (x : Key → ℝ) : Integer.Sparse.eval row17396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17396, Integer.Sparse.eval_collectBalanced, rawRowCheck17396]

def rawRow17397 : Integer.Sparse Key := [(key761, -2), (key766, -2), (key761, -2), (key793, -2), (key766, -2), (key793, -2), (key757, 2), (key769, 2), (key769, 2), (key759, 2), (key766, 2), (key766, 2), (key761, 2), (key793, 2), (key793, 2), (key766, -6), (key768, 2), (key793, 2), (key793, 2), (key769, -6)]

theorem rawRowCheck17397 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form18 = rawRow17397 := by decide +kernel

def row17397 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -6), (key768, 2), (key769, -2), (key793, 4)]

theorem rowCheck17397 : row17397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17397 := by decide +kernel

theorem rowEval17397 (x : Key → ℝ) : Integer.Sparse.eval row17397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form18) x := by
  rw [rowCheck17397, Integer.Sparse.eval_collectBalanced, rawRowCheck17397]

def rawRow17398 : Integer.Sparse Key := [(key766, -2), (key761, -2), (key793, -2), (key761, -2), (key793, -2), (key766, -2), (key769, 2), (key757, 2), (key769, 2), (key766, 2), (key759, 2), (key766, 2), (key793, 2), (key761, 2), (key793, 2), (key766, -6), (key793, 2), (key768, 2), (key793, 2), (key769, -6)]

theorem rawRowCheck17398 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form18 = rawRow17398 := by decide +kernel

def row17398 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -6), (key768, 2), (key769, -2), (key793, 4)]

theorem rowCheck17398 : row17398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17398 := by decide +kernel

theorem rowEval17398 (x : Key → ℝ) : Integer.Sparse.eval row17398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17398, Integer.Sparse.eval_collectBalanced, rawRowCheck17398]

def rawRow17399 : Integer.Sparse Key := [(key793, -2), (key793, -2), (key766, -2), (key766, -2), (key761, -2), (key761, -2), (key769, 2), (key769, 2), (key757, 2), (key766, 2), (key766, 2), (key759, 2), (key793, 2), (key793, 2), (key761, 2), (key766, -6), (key793, 2), (key793, 2), (key768, 2), (key769, -6)]

theorem rawRowCheck17399 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form18 = rawRow17399 := by decide +kernel

def row17399 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -6), (key768, 2), (key769, -2), (key793, 4)]

theorem rowCheck17399 : row17399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17399 := by decide +kernel

theorem rowEval17399 (x : Key → ℝ) : Integer.Sparse.eval row17399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17399, Integer.Sparse.eval_collectBalanced, rawRowCheck17399]

def rawRow17400 : Integer.Sparse Key := [(key768, -2), (key769, -2), (key768, -2), (key793, -2), (key769, -2), (key793, -2), (key759, 2), (key766, 2), (key766, 2), (key757, 2), (key761, 2), (key761, 2), (key766, 2), (key793, 2), (key793, 2), (key761, -6), (key769, 2), (key793, 2), (key793, 2), (key768, -6)]

theorem rawRowCheck17400 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form18 = rawRow17400 := by decide +kernel

def row17400 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, 6), (key768, -10), (key769, -2), (key793, 4)]

theorem rowCheck17400 : row17400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17400 := by decide +kernel

theorem rowEval17400 (x : Key → ℝ) : Integer.Sparse.eval row17400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17400, Integer.Sparse.eval_collectBalanced, rawRowCheck17400]

def rawRow17401 : Integer.Sparse Key := [(key769, -2), (key768, -2), (key793, -2), (key768, -2), (key793, -2), (key769, -2), (key766, 2), (key759, 2), (key766, 2), (key761, 2), (key757, 2), (key761, 2), (key793, 2), (key766, 2), (key793, 2), (key761, -6), (key793, 2), (key769, 2), (key793, 2), (key768, -6)]

theorem rawRowCheck17401 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form18 = rawRow17401 := by decide +kernel

def row17401 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, 6), (key768, -10), (key769, -2), (key793, 4)]

theorem rowCheck17401 : row17401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17401 := by decide +kernel

theorem rowEval17401 (x : Key → ℝ) : Integer.Sparse.eval row17401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17401, Integer.Sparse.eval_collectBalanced, rawRowCheck17401]

def rawRow17402 : Integer.Sparse Key := [(key793, -2), (key793, -2), (key769, -2), (key769, -2), (key768, -2), (key768, -2), (key766, 2), (key766, 2), (key759, 2), (key761, 2), (key761, 2), (key757, 2), (key793, 2), (key793, 2), (key766, 2), (key761, -6), (key793, 2), (key793, 2), (key769, 2), (key768, -6)]

theorem rawRowCheck17402 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form18 = rawRow17402 := by decide +kernel

def row17402 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, 6), (key768, -10), (key769, -2), (key793, 4)]

theorem rowCheck17402 : row17402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17402 := by decide +kernel

theorem rowEval17402 (x : Key → ℝ) : Integer.Sparse.eval row17402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17402, Integer.Sparse.eval_collectBalanced, rawRowCheck17402]

def rawRow17403 : Integer.Sparse Key := [(key761, -2), (key766, -2), (key761, -2), (key793, -2), (key766, -2), (key793, -2), (key761, 2), (key793, 2), (key793, 2), (key766, 2), (key793, 2), (key793, 2), (key757, 2), (key769, 2), (key769, 2), (key769, -6), (key759, 2), (key766, 2), (key766, 2), (key766, -6)]

theorem rawRowCheck17403 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form18 = rawRow17403 := by decide +kernel

def row17403 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -4), (key769, -2), (key793, 4)]

theorem rowCheck17403 : row17403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17403 := by decide +kernel

theorem rowEval17403 (x : Key → ℝ) : Integer.Sparse.eval row17403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form18) x := by
  rw [rowCheck17403, Integer.Sparse.eval_collectBalanced, rawRowCheck17403]

def rawRow17404 : Integer.Sparse Key := [(key766, -2), (key761, -2), (key793, -2), (key761, -2), (key793, -2), (key766, -2), (key793, 2), (key761, 2), (key793, 2), (key793, 2), (key766, 2), (key793, 2), (key769, 2), (key757, 2), (key769, 2), (key769, -6), (key766, 2), (key759, 2), (key766, 2), (key766, -6)]

theorem rawRowCheck17404 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form18 = rawRow17404 := by decide +kernel

def row17404 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -4), (key769, -2), (key793, 4)]

theorem rowCheck17404 : row17404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17404 := by decide +kernel

theorem rowEval17404 (x : Key → ℝ) : Integer.Sparse.eval row17404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17404, Integer.Sparse.eval_collectBalanced, rawRowCheck17404]

def rawRow17405 : Integer.Sparse Key := [(key793, -2), (key793, -2), (key766, -2), (key766, -2), (key761, -2), (key761, -2), (key793, 2), (key793, 2), (key761, 2), (key793, 2), (key793, 2), (key766, 2), (key769, 2), (key769, 2), (key757, 2), (key769, -6), (key766, 2), (key766, 2), (key759, 2), (key766, -6)]

theorem rawRowCheck17405 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form18 = rawRow17405 := by decide +kernel

def row17405 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -4), (key769, -2), (key793, 4)]

theorem rowCheck17405 : row17405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17405 := by decide +kernel

theorem rowEval17405 (x : Key → ℝ) : Integer.Sparse.eval row17405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17405, Integer.Sparse.eval_collectBalanced, rawRowCheck17405]

def rawRow17406 : Integer.Sparse Key := [(key793, -2), (key793, -2), (key793, -2), (key793, -2), (key793, -2), (key793, -2), (key766, 2), (key766, 2), (key766, 2), (key761, 2), (key761, 2), (key761, 2), (key769, 2), (key769, 2), (key769, 2), (key757, -6), (key766, 2), (key766, 2), (key766, 2), (key759, -6)]

theorem rawRowCheck17406 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form18 = rawRow17406 := by decide +kernel

def row17406 : Integer.Sparse Key := [(key757, -6), (key759, -6), (key761, 6), (key766, 12), (key769, 6), (key793, -12)]

theorem rowCheck17406 : row17406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17406 := by decide +kernel

theorem rowEval17406 (x : Key → ℝ) : Integer.Sparse.eval row17406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck17406, Integer.Sparse.eval_collectBalanced, rawRowCheck17406]

def rawRow17407 : Integer.Sparse Key := [(key768, -2), (key769, -2), (key768, -2), (key793, -2), (key769, -2), (key793, -2), (key768, 2), (key793, 2), (key793, 2), (key769, 2), (key793, 2), (key793, 2), (key759, 2), (key766, 2), (key766, 2), (key766, -6), (key757, 2), (key761, 2), (key761, 2), (key761, -6)]

theorem rawRowCheck17407 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form18 = rawRow17407 := by decide +kernel

def row17407 : Integer.Sparse Key := [(key757, 2), (key759, 2), (key761, -2), (key766, -2), (key768, -2), (key769, -2), (key793, 4)]

theorem rowCheck17407 : row17407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17407 := by decide +kernel

theorem rowEval17407 (x : Key → ℝ) : Integer.Sparse.eval row17407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck17407, Integer.Sparse.eval_collectBalanced, rawRowCheck17407]

end MUB6.Certificate.GramRows

end OAI
