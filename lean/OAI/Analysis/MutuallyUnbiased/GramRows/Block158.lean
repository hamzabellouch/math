import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block2
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block6
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow17152 : Integer.Sparse Key := [(key2019, -1), (key2013, -1), (key2134, -1), (key2127, -1), (key2145, -1), (key2144, -1), (key2026, 2), (key2145, 2), (key2144, 2), (key2019, -1), (key2013, -1), (key2134, -1), (key2127, -1), (key2145, -1), (key2144, -1), (key2047, 2), (key2042, 2), (key2134, 2), (key2127, 2), (key2229, 2), (key2228, 2), (key2056, -1), (key2055, -1), (key2145, -1), (key2144, -1), (key2229, -1), (key2228, -1), (key2026, 2), (key2145, 2), (key2144, 2), (key2056, -1), (key2055, -1), (key2145, -1), (key2144, -1), (key2229, -1), (key2228, -1)]

theorem rawRowCheck17152 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form6 = rawRow17152 := by decide +kernel

def row17152 : Integer.Sparse Key := [(key2013, -2), (key2019, -2), (key2026, 4), (key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2)]

theorem rowCheck17152 : row17152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17152 := by decide +kernel

theorem rowEval17152 (x : Key → ℝ) : Integer.Sparse.eval row17152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17152, Integer.Sparse.eval_collectBalanced, rawRowCheck17152]

def rawRow17153 : Integer.Sparse Key := [(key2127, -1), (key2144, -1), (key2013, -1), (key2145, -1), (key2019, -1), (key2134, -1), (key2144, 2), (key2026, 2), (key2145, 2), (key2127, -1), (key2144, -1), (key2013, -1), (key2145, -1), (key2019, -1), (key2134, -1), (key2127, 2), (key2228, 2), (key2042, 2), (key2229, 2), (key2047, 2), (key2134, 2), (key2144, -1), (key2228, -1), (key2055, -1), (key2229, -1), (key2056, -1), (key2145, -1), (key2144, 2), (key2026, 2), (key2145, 2), (key2144, -1), (key2228, -1), (key2055, -1), (key2229, -1), (key2056, -1), (key2145, -1)]

theorem rawRowCheck17153 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form6 = rawRow17153 := by decide +kernel

def row17153 : Integer.Sparse Key := [(key2013, -2), (key2019, -2), (key2026, 4), (key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2)]

theorem rowCheck17153 : row17153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17153 := by decide +kernel

theorem rowEval17153 (x : Key → ℝ) : Integer.Sparse.eval row17153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck17153, Integer.Sparse.eval_collectBalanced, rawRowCheck17153]

def rawRow17154 : Integer.Sparse Key := [(key2144, -1), (key2127, -1), (key2145, -1), (key2013, -1), (key2134, -1), (key2019, -1), (key2144, 2), (key2145, 2), (key2026, 2), (key2144, -1), (key2127, -1), (key2145, -1), (key2013, -1), (key2134, -1), (key2019, -1), (key2228, 2), (key2127, 2), (key2229, 2), (key2042, 2), (key2134, 2), (key2047, 2), (key2228, -1), (key2144, -1), (key2229, -1), (key2055, -1), (key2145, -1), (key2056, -1), (key2144, 2), (key2145, 2), (key2026, 2), (key2228, -1), (key2144, -1), (key2229, -1), (key2055, -1), (key2145, -1), (key2056, -1)]

theorem rawRowCheck17154 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form6 = rawRow17154 := by decide +kernel

def row17154 : Integer.Sparse Key := [(key2013, -2), (key2019, -2), (key2026, 4), (key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2)]

theorem rowCheck17154 : row17154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17154 := by decide +kernel

theorem rowEval17154 (x : Key → ℝ) : Integer.Sparse.eval row17154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17154, Integer.Sparse.eval_collectBalanced, rawRowCheck17154]

def rawRow17155 : Integer.Sparse Key := [(key2134, -1), (key2145, -1), (key2019, -1), (key2144, -1), (key2013, -1), (key2127, -1), (key2145, 2), (key2026, 2), (key2144, 2), (key2134, -1), (key2145, -1), (key2019, -1), (key2144, -1), (key2013, -1), (key2127, -1), (key2134, 2), (key2229, 2), (key2047, 2), (key2228, 2), (key2042, 2), (key2127, 2), (key2145, -1), (key2229, -1), (key2056, -1), (key2228, -1), (key2055, -1), (key2144, -1), (key2145, 2), (key2026, 2), (key2144, 2), (key2145, -1), (key2229, -1), (key2056, -1), (key2228, -1), (key2055, -1), (key2144, -1)]

theorem rawRowCheck17155 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form6 = rawRow17155 := by decide +kernel

def row17155 : Integer.Sparse Key := [(key2013, -2), (key2019, -2), (key2026, 4), (key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2)]

theorem rowCheck17155 : row17155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17155 := by decide +kernel

theorem rowEval17155 (x : Key → ℝ) : Integer.Sparse.eval row17155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17155, Integer.Sparse.eval_collectBalanced, rawRowCheck17155]

def rawRow17156 : Integer.Sparse Key := [(key2145, -1), (key2134, -1), (key2144, -1), (key2019, -1), (key2127, -1), (key2013, -1), (key2145, 2), (key2144, 2), (key2026, 2), (key2145, -1), (key2134, -1), (key2144, -1), (key2019, -1), (key2127, -1), (key2013, -1), (key2229, 2), (key2134, 2), (key2228, 2), (key2047, 2), (key2127, 2), (key2042, 2), (key2229, -1), (key2145, -1), (key2228, -1), (key2056, -1), (key2144, -1), (key2055, -1), (key2145, 2), (key2144, 2), (key2026, 2), (key2229, -1), (key2145, -1), (key2228, -1), (key2056, -1), (key2144, -1), (key2055, -1)]

theorem rawRowCheck17156 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form6 = rawRow17156 := by decide +kernel

def row17156 : Integer.Sparse Key := [(key2013, -2), (key2019, -2), (key2026, 4), (key2042, 2), (key2047, 2), (key2055, -2), (key2056, -2)]

theorem rowCheck17156 : row17156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17156 := by decide +kernel

theorem rowEval17156 (x : Key → ℝ) : Integer.Sparse.eval row17156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17156, Integer.Sparse.eval_collectBalanced, rawRowCheck17156]

def rawRow17157 : Integer.Sparse Key := [(key2013, -1), (key2026, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2145, -1), (key2019, 2), (key2019, 2), (key2134, 2), (key2042, -1), (key2055, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2229, -1), (key2013, 2), (key2056, 2), (key2013, 2), (key2145, 2), (key2056, 2), (key2145, 2), (key2019, -1), (key2047, -1), (key2019, -1), (key2134, -1), (key2047, -1), (key2134, -1), (key2055, 2), (key2055, 2), (key2229, 2), (key2026, -1), (key2056, -1), (key2026, -1), (key2145, -1), (key2056, -1), (key2145, -1)]

theorem rawRowCheck17157 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form6 = rawRow17157 := by decide +kernel

def row17157 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

theorem rowCheck17157 : row17157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17157 := by decide +kernel

theorem rowEval17157 (x : Key → ℝ) : Integer.Sparse.eval row17157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck17157, Integer.Sparse.eval_collectBalanced, rawRowCheck17157]

def rawRow17158 : Integer.Sparse Key := [(key2026, -1), (key2013, -1), (key2145, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2019, 2), (key2134, 2), (key2019, 2), (key2055, -1), (key2042, -1), (key2229, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2056, 2), (key2013, 2), (key2145, 2), (key2013, 2), (key2145, 2), (key2056, 2), (key2047, -1), (key2019, -1), (key2134, -1), (key2019, -1), (key2134, -1), (key2047, -1), (key2055, 2), (key2229, 2), (key2055, 2), (key2056, -1), (key2026, -1), (key2145, -1), (key2026, -1), (key2145, -1), (key2056, -1)]

theorem rawRowCheck17158 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form6 = rawRow17158 := by decide +kernel

def row17158 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

theorem rowCheck17158 : row17158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17158 := by decide +kernel

theorem rowEval17158 (x : Key → ℝ) : Integer.Sparse.eval row17158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17158, Integer.Sparse.eval_collectBalanced, rawRowCheck17158]

def rawRow17159 : Integer.Sparse Key := [(key2145, -1), (key2145, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2134, 2), (key2019, 2), (key2019, 2), (key2229, -1), (key2229, -1), (key2055, -1), (key2055, -1), (key2042, -1), (key2042, -1), (key2145, 2), (key2145, 2), (key2056, 2), (key2056, 2), (key2013, 2), (key2013, 2), (key2134, -1), (key2134, -1), (key2047, -1), (key2047, -1), (key2019, -1), (key2019, -1), (key2229, 2), (key2055, 2), (key2055, 2), (key2145, -1), (key2145, -1), (key2056, -1), (key2056, -1), (key2026, -1), (key2026, -1)]

theorem rawRowCheck17159 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form6 = rawRow17159 := by decide +kernel

def row17159 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

theorem rowCheck17159 : row17159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17159 := by decide +kernel

theorem rowEval17159 (x : Key → ℝ) : Integer.Sparse.eval row17159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17159, Integer.Sparse.eval_collectBalanced, rawRowCheck17159]

def rawRow17160 : Integer.Sparse Key := [(key2019, -1), (key2026, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2144, -1), (key2013, 2), (key2013, 2), (key2127, 2), (key2047, -1), (key2056, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2228, -1), (key2019, 2), (key2055, 2), (key2019, 2), (key2144, 2), (key2055, 2), (key2144, 2), (key2013, -1), (key2042, -1), (key2013, -1), (key2127, -1), (key2042, -1), (key2127, -1), (key2056, 2), (key2056, 2), (key2228, 2), (key2026, -1), (key2055, -1), (key2026, -1), (key2144, -1), (key2055, -1), (key2144, -1)]

theorem rawRowCheck17160 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form6 = rawRow17160 := by decide +kernel

def row17160 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

theorem rowCheck17160 : row17160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17160 := by decide +kernel

theorem rowEval17160 (x : Key → ℝ) : Integer.Sparse.eval row17160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17160, Integer.Sparse.eval_collectBalanced, rawRowCheck17160]

def rawRow17161 : Integer.Sparse Key := [(key2026, -1), (key2019, -1), (key2144, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2013, 2), (key2127, 2), (key2013, 2), (key2056, -1), (key2047, -1), (key2228, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2055, 2), (key2019, 2), (key2144, 2), (key2019, 2), (key2144, 2), (key2055, 2), (key2042, -1), (key2013, -1), (key2127, -1), (key2013, -1), (key2127, -1), (key2042, -1), (key2056, 2), (key2228, 2), (key2056, 2), (key2055, -1), (key2026, -1), (key2144, -1), (key2026, -1), (key2144, -1), (key2055, -1)]

theorem rawRowCheck17161 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form6 = rawRow17161 := by decide +kernel

def row17161 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

theorem rowCheck17161 : row17161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17161 := by decide +kernel

theorem rowEval17161 (x : Key → ℝ) : Integer.Sparse.eval row17161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17161, Integer.Sparse.eval_collectBalanced, rawRowCheck17161]

def rawRow17162 : Integer.Sparse Key := [(key2144, -1), (key2144, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2127, 2), (key2013, 2), (key2013, 2), (key2228, -1), (key2228, -1), (key2056, -1), (key2056, -1), (key2047, -1), (key2047, -1), (key2144, 2), (key2144, 2), (key2055, 2), (key2055, 2), (key2019, 2), (key2019, 2), (key2127, -1), (key2127, -1), (key2042, -1), (key2042, -1), (key2013, -1), (key2013, -1), (key2228, 2), (key2056, 2), (key2056, 2), (key2144, -1), (key2144, -1), (key2055, -1), (key2055, -1), (key2026, -1), (key2026, -1)]

theorem rawRowCheck17162 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form6 = rawRow17162 := by decide +kernel

def row17162 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

theorem rowCheck17162 : row17162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17162 := by decide +kernel

theorem rowEval17162 (x : Key → ℝ) : Integer.Sparse.eval row17162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17162, Integer.Sparse.eval_collectBalanced, rawRowCheck17162]

def rawRow17163 : Integer.Sparse Key := [(key2042, -1), (key2055, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2229, -1), (key2055, 2), (key2055, 2), (key2229, 2), (key2013, -1), (key2026, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2145, -1), (key2013, 2), (key2056, 2), (key2013, 2), (key2145, 2), (key2056, 2), (key2145, 2), (key2026, -1), (key2056, -1), (key2026, -1), (key2145, -1), (key2056, -1), (key2145, -1), (key2019, 2), (key2019, 2), (key2134, 2), (key2019, -1), (key2047, -1), (key2019, -1), (key2134, -1), (key2047, -1), (key2134, -1)]

theorem rawRowCheck17163 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form6 = rawRow17163 := by decide +kernel

def row17163 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

theorem rowCheck17163 : row17163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17163 := by decide +kernel

theorem rowEval17163 (x : Key → ℝ) : Integer.Sparse.eval row17163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form6) x := by
  rw [rowCheck17163, Integer.Sparse.eval_collectBalanced, rawRowCheck17163]

def rawRow17164 : Integer.Sparse Key := [(key2055, -1), (key2042, -1), (key2229, -1), (key2042, -1), (key2229, -1), (key2055, -1), (key2055, 2), (key2229, 2), (key2055, 2), (key2026, -1), (key2013, -1), (key2145, -1), (key2013, -1), (key2145, -1), (key2026, -1), (key2056, 2), (key2013, 2), (key2145, 2), (key2013, 2), (key2145, 2), (key2056, 2), (key2056, -1), (key2026, -1), (key2145, -1), (key2026, -1), (key2145, -1), (key2056, -1), (key2019, 2), (key2134, 2), (key2019, 2), (key2047, -1), (key2019, -1), (key2134, -1), (key2019, -1), (key2134, -1), (key2047, -1)]

theorem rawRowCheck17164 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form6 = rawRow17164 := by decide +kernel

def row17164 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

theorem rowCheck17164 : row17164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17164 := by decide +kernel

theorem rowEval17164 (x : Key → ℝ) : Integer.Sparse.eval row17164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17164, Integer.Sparse.eval_collectBalanced, rawRowCheck17164]

def rawRow17165 : Integer.Sparse Key := [(key2229, -1), (key2229, -1), (key2055, -1), (key2055, -1), (key2042, -1), (key2042, -1), (key2229, 2), (key2055, 2), (key2055, 2), (key2145, -1), (key2145, -1), (key2026, -1), (key2026, -1), (key2013, -1), (key2013, -1), (key2145, 2), (key2145, 2), (key2056, 2), (key2056, 2), (key2013, 2), (key2013, 2), (key2145, -1), (key2145, -1), (key2056, -1), (key2056, -1), (key2026, -1), (key2026, -1), (key2134, 2), (key2019, 2), (key2019, 2), (key2134, -1), (key2134, -1), (key2047, -1), (key2047, -1), (key2019, -1), (key2019, -1)]

theorem rawRowCheck17165 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form6 = rawRow17165 := by decide +kernel

def row17165 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

theorem rowCheck17165 : row17165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17165 := by decide +kernel

theorem rowEval17165 (x : Key → ℝ) : Integer.Sparse.eval row17165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17165, Integer.Sparse.eval_collectBalanced, rawRowCheck17165]

def rawRow17166 : Integer.Sparse Key := [(key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2042, 2), (key2042, 2), (key2042, 2), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2013, -1), (key2013, -1), (key2013, -1), (key2013, -1), (key2013, -1), (key2013, -1), (key2047, 2), (key2047, 2), (key2047, 2), (key2019, -1), (key2019, -1), (key2019, -1), (key2019, -1), (key2019, -1), (key2019, -1)]

theorem rawRowCheck17166 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form6 = rawRow17166 := by decide +kernel

def row17166 : Integer.Sparse Key := [(key2013, -6), (key2019, -6), (key2026, 12), (key2042, 6), (key2047, 6), (key2055, -6), (key2056, -6)]

theorem rowCheck17166 : row17166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17166 := by decide +kernel

theorem rowEval17166 (x : Key → ℝ) : Integer.Sparse.eval row17166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17166, Integer.Sparse.eval_collectBalanced, rawRowCheck17166]

def rawRow17167 : Integer.Sparse Key := [(key2047, -1), (key2056, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2228, -1), (key2056, 2), (key2056, 2), (key2228, 2), (key2019, -1), (key2026, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2144, -1), (key2019, 2), (key2055, 2), (key2019, 2), (key2144, 2), (key2055, 2), (key2144, 2), (key2026, -1), (key2055, -1), (key2026, -1), (key2144, -1), (key2055, -1), (key2144, -1), (key2013, 2), (key2013, 2), (key2127, 2), (key2013, -1), (key2042, -1), (key2013, -1), (key2127, -1), (key2042, -1), (key2127, -1)]

theorem rawRowCheck17167 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form6 = rawRow17167 := by decide +kernel

def row17167 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

theorem rowCheck17167 : row17167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17167 := by decide +kernel

theorem rowEval17167 (x : Key → ℝ) : Integer.Sparse.eval row17167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck17167, Integer.Sparse.eval_collectBalanced, rawRowCheck17167]

def rawRow17168 : Integer.Sparse Key := [(key2056, -1), (key2047, -1), (key2228, -1), (key2047, -1), (key2228, -1), (key2056, -1), (key2056, 2), (key2228, 2), (key2056, 2), (key2026, -1), (key2019, -1), (key2144, -1), (key2019, -1), (key2144, -1), (key2026, -1), (key2055, 2), (key2019, 2), (key2144, 2), (key2019, 2), (key2144, 2), (key2055, 2), (key2055, -1), (key2026, -1), (key2144, -1), (key2026, -1), (key2144, -1), (key2055, -1), (key2013, 2), (key2127, 2), (key2013, 2), (key2042, -1), (key2013, -1), (key2127, -1), (key2013, -1), (key2127, -1), (key2042, -1)]

theorem rawRowCheck17168 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form6 = rawRow17168 := by decide +kernel

def row17168 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

theorem rowCheck17168 : row17168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17168 := by decide +kernel

theorem rowEval17168 (x : Key → ℝ) : Integer.Sparse.eval row17168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17168, Integer.Sparse.eval_collectBalanced, rawRowCheck17168]

def rawRow17169 : Integer.Sparse Key := [(key2228, -1), (key2228, -1), (key2056, -1), (key2056, -1), (key2047, -1), (key2047, -1), (key2228, 2), (key2056, 2), (key2056, 2), (key2144, -1), (key2144, -1), (key2026, -1), (key2026, -1), (key2019, -1), (key2019, -1), (key2144, 2), (key2144, 2), (key2055, 2), (key2055, 2), (key2019, 2), (key2019, 2), (key2144, -1), (key2144, -1), (key2055, -1), (key2055, -1), (key2026, -1), (key2026, -1), (key2127, 2), (key2013, 2), (key2013, 2), (key2127, -1), (key2127, -1), (key2042, -1), (key2042, -1), (key2013, -1), (key2013, -1)]

theorem rawRowCheck17169 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form6 = rawRow17169 := by decide +kernel

def row17169 : Integer.Sparse Key := [(key2013, 2), (key2019, 2), (key2026, -4), (key2042, -2), (key2047, -2), (key2055, 2), (key2056, 2)]

theorem rowCheck17169 : row17169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17169 := by decide +kernel

theorem rowEval17169 (x : Key → ℝ) : Integer.Sparse.eval row17169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17169, Integer.Sparse.eval_collectBalanced, rawRowCheck17169]

def rawRow17170 : Integer.Sparse Key := [(key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2056, -1), (key2047, 2), (key2047, 2), (key2047, 2), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2055, -1), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2026, 2), (key2019, -1), (key2019, -1), (key2019, -1), (key2019, -1), (key2019, -1), (key2019, -1), (key2042, 2), (key2042, 2), (key2042, 2), (key2013, -1), (key2013, -1), (key2013, -1), (key2013, -1), (key2013, -1), (key2013, -1)]

theorem rawRowCheck17170 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form6 = rawRow17170 := by decide +kernel

def row17170 : Integer.Sparse Key := [(key2013, -6), (key2019, -6), (key2026, 12), (key2042, 6), (key2047, 6), (key2055, -6), (key2056, -6)]

theorem rowCheck17170 : row17170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17170 := by decide +kernel

theorem rowEval17170 (x : Key → ℝ) : Integer.Sparse.eval row17170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form6) x := by
  rw [rowCheck17170, Integer.Sparse.eval_collectBalanced, rawRowCheck17170]

def rawRow17171 : Integer.Sparse Key := [(key2103, 4), (key2108, 4), (key2109, 4), (key2108, -4), (key2109, -4), (key2131, -4), (key2108, -4), (key2109, -4), (key2131, -4), (key2131, 12)]

theorem rawRowCheck17171 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form7 = rawRow17171 := by decide +kernel

def row17171 : Integer.Sparse Key := [(key2103, 4), (key2108, -4), (key2109, -4), (key2131, 4)]

theorem rowCheck17171 : row17171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17171 := by decide +kernel

theorem rowEval17171 (x : Key → ℝ) : Integer.Sparse.eval row17171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck17171, Integer.Sparse.eval_collectBalanced, rawRowCheck17171]

def rawRow17172 : Integer.Sparse Key := [(key2103, 4), (key2109, 4), (key2108, 4), (key2109, -4), (key2108, -4), (key2131, -4), (key2109, -4), (key2108, -4), (key2131, -4), (key2131, 12)]

theorem rawRowCheck17172 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form7 = rawRow17172 := by decide +kernel

def row17172 : Integer.Sparse Key := [(key2103, 4), (key2108, -4), (key2109, -4), (key2131, 4)]

theorem rowCheck17172 : row17172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17172 := by decide +kernel

theorem rowEval17172 (x : Key → ℝ) : Integer.Sparse.eval row17172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17172, Integer.Sparse.eval_collectBalanced, rawRowCheck17172]

def rawRow17173 : Integer.Sparse Key := [(key2108, 4), (key2103, 4), (key2109, 4), (key2108, -4), (key2131, -4), (key2109, -4), (key2108, -4), (key2131, -4), (key2109, -4), (key2131, 12)]

theorem rawRowCheck17173 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form7 = rawRow17173 := by decide +kernel

def row17173 : Integer.Sparse Key := [(key2103, 4), (key2108, -4), (key2109, -4), (key2131, 4)]

theorem rowCheck17173 : row17173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17173 := by decide +kernel

theorem rowEval17173 (x : Key → ℝ) : Integer.Sparse.eval row17173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck17173, Integer.Sparse.eval_collectBalanced, rawRowCheck17173]

def rawRow17174 : Integer.Sparse Key := [(key2108, 4), (key2109, 4), (key2103, 4), (key2131, -4), (key2108, -4), (key2109, -4), (key2131, -4), (key2108, -4), (key2109, -4), (key2131, 12)]

theorem rawRowCheck17174 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form7 = rawRow17174 := by decide +kernel

def row17174 : Integer.Sparse Key := [(key2103, 4), (key2108, -4), (key2109, -4), (key2131, 4)]

theorem rowCheck17174 : row17174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17174 := by decide +kernel

theorem rowEval17174 (x : Key → ℝ) : Integer.Sparse.eval row17174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17174, Integer.Sparse.eval_collectBalanced, rawRowCheck17174]

def rawRow17175 : Integer.Sparse Key := [(key2109, 4), (key2103, 4), (key2108, 4), (key2109, -4), (key2131, -4), (key2108, -4), (key2109, -4), (key2131, -4), (key2108, -4), (key2131, 12)]

theorem rawRowCheck17175 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form7 = rawRow17175 := by decide +kernel

def row17175 : Integer.Sparse Key := [(key2103, 4), (key2108, -4), (key2109, -4), (key2131, 4)]

theorem rowCheck17175 : row17175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17175 := by decide +kernel

theorem rowEval17175 (x : Key → ℝ) : Integer.Sparse.eval row17175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17175, Integer.Sparse.eval_collectBalanced, rawRowCheck17175]

def rawRow17176 : Integer.Sparse Key := [(key2109, 4), (key2108, 4), (key2103, 4), (key2131, -4), (key2109, -4), (key2108, -4), (key2131, -4), (key2109, -4), (key2108, -4), (key2131, 12)]

theorem rawRowCheck17176 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form7 = rawRow17176 := by decide +kernel

def row17176 : Integer.Sparse Key := [(key2103, 4), (key2108, -4), (key2109, -4), (key2131, 4)]

theorem rowCheck17176 : row17176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17176 := by decide +kernel

theorem rowEval17176 (x : Key → ℝ) : Integer.Sparse.eval row17176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17176, Integer.Sparse.eval_collectBalanced, rawRowCheck17176]

def rawRow17177 : Integer.Sparse Key := [(key2108, 4), (key2108, 4), (key2131, 4), (key2103, -4), (key2109, -4), (key2109, -4), (key2108, -4), (key2131, -4), (key2131, -4), (key2109, 12)]

theorem rawRowCheck17177 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form7 = rawRow17177 := by decide +kernel

def row17177 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

theorem rowCheck17177 : row17177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17177 := by decide +kernel

theorem rowEval17177 (x : Key → ℝ) : Integer.Sparse.eval row17177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck17177, Integer.Sparse.eval_collectBalanced, rawRowCheck17177]

def rawRow17178 : Integer.Sparse Key := [(key2108, 4), (key2131, 4), (key2108, 4), (key2109, -4), (key2103, -4), (key2109, -4), (key2131, -4), (key2108, -4), (key2131, -4), (key2109, 12)]

theorem rawRowCheck17178 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form7 = rawRow17178 := by decide +kernel

def row17178 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

theorem rowCheck17178 : row17178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17178 := by decide +kernel

theorem rowEval17178 (x : Key → ℝ) : Integer.Sparse.eval row17178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17178, Integer.Sparse.eval_collectBalanced, rawRowCheck17178]

def rawRow17179 : Integer.Sparse Key := [(key2131, 4), (key2108, 4), (key2108, 4), (key2109, -4), (key2109, -4), (key2103, -4), (key2131, -4), (key2131, -4), (key2108, -4), (key2109, 12)]

theorem rawRowCheck17179 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form7 = rawRow17179 := by decide +kernel

def row17179 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

theorem rowCheck17179 : row17179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17179 := by decide +kernel

theorem rowEval17179 (x : Key → ℝ) : Integer.Sparse.eval row17179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17179, Integer.Sparse.eval_collectBalanced, rawRowCheck17179]

def rawRow17180 : Integer.Sparse Key := [(key2109, 4), (key2109, 4), (key2131, 4), (key2103, -4), (key2108, -4), (key2108, -4), (key2109, -4), (key2131, -4), (key2131, -4), (key2108, 12)]

theorem rawRowCheck17180 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form7 = rawRow17180 := by decide +kernel

def row17180 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

theorem rowCheck17180 : row17180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17180 := by decide +kernel

theorem rowEval17180 (x : Key → ℝ) : Integer.Sparse.eval row17180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17180, Integer.Sparse.eval_collectBalanced, rawRowCheck17180]

def rawRow17181 : Integer.Sparse Key := [(key2109, 4), (key2131, 4), (key2109, 4), (key2108, -4), (key2103, -4), (key2108, -4), (key2131, -4), (key2109, -4), (key2131, -4), (key2108, 12)]

theorem rawRowCheck17181 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form7 = rawRow17181 := by decide +kernel

def row17181 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

theorem rowCheck17181 : row17181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17181 := by decide +kernel

theorem rowEval17181 (x : Key → ℝ) : Integer.Sparse.eval row17181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17181, Integer.Sparse.eval_collectBalanced, rawRowCheck17181]

def rawRow17182 : Integer.Sparse Key := [(key2131, 4), (key2109, 4), (key2109, 4), (key2108, -4), (key2108, -4), (key2103, -4), (key2131, -4), (key2131, -4), (key2109, -4), (key2108, 12)]

theorem rawRowCheck17182 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form7 = rawRow17182 := by decide +kernel

def row17182 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

theorem rowCheck17182 : row17182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17182 := by decide +kernel

theorem rowEval17182 (x : Key → ℝ) : Integer.Sparse.eval row17182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17182, Integer.Sparse.eval_collectBalanced, rawRowCheck17182]

def rawRow17183 : Integer.Sparse Key := [(key2108, 4), (key2108, 4), (key2131, 4), (key2108, -4), (key2131, -4), (key2131, -4), (key2103, -4), (key2109, -4), (key2109, -4), (key2109, 12)]

theorem rawRowCheck17183 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form7 = rawRow17183 := by decide +kernel

def row17183 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

theorem rowCheck17183 : row17183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17183 := by decide +kernel

theorem rowEval17183 (x : Key → ℝ) : Integer.Sparse.eval row17183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form7) x := by
  rw [rowCheck17183, Integer.Sparse.eval_collectBalanced, rawRowCheck17183]

def rawRow17184 : Integer.Sparse Key := [(key2108, 4), (key2131, 4), (key2108, 4), (key2131, -4), (key2108, -4), (key2131, -4), (key2109, -4), (key2103, -4), (key2109, -4), (key2109, 12)]

theorem rawRowCheck17184 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form7 = rawRow17184 := by decide +kernel

def row17184 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

theorem rowCheck17184 : row17184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17184 := by decide +kernel

theorem rowEval17184 (x : Key → ℝ) : Integer.Sparse.eval row17184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17184, Integer.Sparse.eval_collectBalanced, rawRowCheck17184]

def rawRow17185 : Integer.Sparse Key := [(key2131, 4), (key2108, 4), (key2108, 4), (key2131, -4), (key2131, -4), (key2108, -4), (key2109, -4), (key2109, -4), (key2103, -4), (key2109, 12)]

theorem rawRowCheck17185 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form7 = rawRow17185 := by decide +kernel

def row17185 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

theorem rowCheck17185 : row17185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17185 := by decide +kernel

theorem rowEval17185 (x : Key → ℝ) : Integer.Sparse.eval row17185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17185, Integer.Sparse.eval_collectBalanced, rawRowCheck17185]

def rawRow17186 : Integer.Sparse Key := [(key2131, 4), (key2131, 4), (key2131, 4), (key2108, -4), (key2108, -4), (key2108, -4), (key2109, -4), (key2109, -4), (key2109, -4), (key2103, 12)]

theorem rawRowCheck17186 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form7 = rawRow17186 := by decide +kernel

def row17186 : Integer.Sparse Key := [(key2103, 12), (key2108, -12), (key2109, -12), (key2131, 12)]

theorem rowCheck17186 : row17186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17186 := by decide +kernel

theorem rowEval17186 (x : Key → ℝ) : Integer.Sparse.eval row17186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17186, Integer.Sparse.eval_collectBalanced, rawRowCheck17186]

def rawRow17187 : Integer.Sparse Key := [(key2109, 4), (key2109, 4), (key2131, 4), (key2109, -4), (key2131, -4), (key2131, -4), (key2103, -4), (key2108, -4), (key2108, -4), (key2108, 12)]

theorem rawRowCheck17187 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form7 = rawRow17187 := by decide +kernel

def row17187 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

theorem rowCheck17187 : row17187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17187 := by decide +kernel

theorem rowEval17187 (x : Key → ℝ) : Integer.Sparse.eval row17187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck17187, Integer.Sparse.eval_collectBalanced, rawRowCheck17187]

def rawRow17188 : Integer.Sparse Key := [(key2109, 4), (key2131, 4), (key2109, 4), (key2131, -4), (key2109, -4), (key2131, -4), (key2108, -4), (key2103, -4), (key2108, -4), (key2108, 12)]

theorem rawRowCheck17188 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form7 = rawRow17188 := by decide +kernel

def row17188 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

theorem rowCheck17188 : row17188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17188 := by decide +kernel

theorem rowEval17188 (x : Key → ℝ) : Integer.Sparse.eval row17188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17188, Integer.Sparse.eval_collectBalanced, rawRowCheck17188]

def rawRow17189 : Integer.Sparse Key := [(key2131, 4), (key2109, 4), (key2109, 4), (key2131, -4), (key2131, -4), (key2109, -4), (key2108, -4), (key2108, -4), (key2103, -4), (key2108, 12)]

theorem rawRowCheck17189 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form7 = rawRow17189 := by decide +kernel

def row17189 : Integer.Sparse Key := [(key2103, -4), (key2108, 4), (key2109, 4), (key2131, -4)]

theorem rowCheck17189 : row17189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17189 := by decide +kernel

theorem rowEval17189 (x : Key → ℝ) : Integer.Sparse.eval row17189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17189, Integer.Sparse.eval_collectBalanced, rawRowCheck17189]

def rawRow17190 : Integer.Sparse Key := [(key2131, 4), (key2131, 4), (key2131, 4), (key2109, -4), (key2109, -4), (key2109, -4), (key2108, -4), (key2108, -4), (key2108, -4), (key2103, 12)]

theorem rawRowCheck17190 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form7 = rawRow17190 := by decide +kernel

def row17190 : Integer.Sparse Key := [(key2103, 12), (key2108, -12), (key2109, -12), (key2131, 12)]

theorem rowCheck17190 : row17190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17190 := by decide +kernel

theorem rowEval17190 (x : Key → ℝ) : Integer.Sparse.eval row17190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck17190, Integer.Sparse.eval_collectBalanced, rawRowCheck17190]

def rawRow17191 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, -2), (key1982, 6), (key1974, -2), (key1977, -2), (key1982, -2), (key1974, 2), (key1977, 2), (key2210, 2), (key2214, 2), (key2219, 2), (key2223, 2), (key1982, -2), (key2219, -2), (key2223, -2), (key1982, 6), (key1982, -2), (key2219, -2), (key2223, -2)]

theorem rawRowCheck17191 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form8 = rawRow17191 := by decide +kernel

def row17191 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, 4), (key2210, 2), (key2214, 2), (key2219, -2), (key2223, -2)]

theorem rowCheck17191 : row17191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17191 := by decide +kernel

theorem rowEval17191 (x : Key → ℝ) : Integer.Sparse.eval row17191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck17191, Integer.Sparse.eval_collectBalanced, rawRowCheck17191]

def rawRow17192 : Integer.Sparse Key := [(key1977, -2), (key1974, -2), (key1982, -2), (key1982, 6), (key1977, -2), (key1974, -2), (key1982, -2), (key1977, 2), (key1974, 2), (key2214, 2), (key2210, 2), (key2223, 2), (key2219, 2), (key1982, -2), (key2223, -2), (key2219, -2), (key1982, 6), (key1982, -2), (key2223, -2), (key2219, -2)]

theorem rawRowCheck17192 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form8 = rawRow17192 := by decide +kernel

def row17192 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, 4), (key2210, 2), (key2214, 2), (key2219, -2), (key2223, -2)]

theorem rowCheck17192 : row17192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17192 := by decide +kernel

theorem rowEval17192 (x : Key → ℝ) : Integer.Sparse.eval row17192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17192, Integer.Sparse.eval_collectBalanced, rawRowCheck17192]

def rawRow17193 : Integer.Sparse Key := [(key1974, -2), (key1982, -2), (key1977, -2), (key1982, 6), (key1974, -2), (key1982, -2), (key1977, -2), (key2210, 2), (key2219, 2), (key1974, 2), (key2223, 2), (key1977, 2), (key2214, 2), (key2219, -2), (key1982, -2), (key2223, -2), (key1982, 6), (key2219, -2), (key1982, -2), (key2223, -2)]

theorem rawRowCheck17193 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form8 = rawRow17193 := by decide +kernel

def row17193 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, 4), (key2210, 2), (key2214, 2), (key2219, -2), (key2223, -2)]

theorem rowCheck17193 : row17193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17193 := by decide +kernel

theorem rowEval17193 (x : Key → ℝ) : Integer.Sparse.eval row17193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck17193, Integer.Sparse.eval_collectBalanced, rawRowCheck17193]

def rawRow17194 : Integer.Sparse Key := [(key1982, -2), (key1974, -2), (key1977, -2), (key1982, 6), (key1982, -2), (key1974, -2), (key1977, -2), (key2219, 2), (key2210, 2), (key2223, 2), (key1974, 2), (key2214, 2), (key1977, 2), (key2219, -2), (key2223, -2), (key1982, -2), (key1982, 6), (key2219, -2), (key2223, -2), (key1982, -2)]

theorem rawRowCheck17194 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form8 = rawRow17194 := by decide +kernel

def row17194 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, 4), (key2210, 2), (key2214, 2), (key2219, -2), (key2223, -2)]

theorem rowCheck17194 : row17194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17194 := by decide +kernel

theorem rowEval17194 (x : Key → ℝ) : Integer.Sparse.eval row17194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17194, Integer.Sparse.eval_collectBalanced, rawRowCheck17194]

def rawRow17195 : Integer.Sparse Key := [(key1977, -2), (key1982, -2), (key1974, -2), (key1982, 6), (key1977, -2), (key1982, -2), (key1974, -2), (key2214, 2), (key2223, 2), (key1977, 2), (key2219, 2), (key1974, 2), (key2210, 2), (key2223, -2), (key1982, -2), (key2219, -2), (key1982, 6), (key2223, -2), (key1982, -2), (key2219, -2)]

theorem rawRowCheck17195 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form8 = rawRow17195 := by decide +kernel

def row17195 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, 4), (key2210, 2), (key2214, 2), (key2219, -2), (key2223, -2)]

theorem rowCheck17195 : row17195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17195 := by decide +kernel

theorem rowEval17195 (x : Key → ℝ) : Integer.Sparse.eval row17195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17195, Integer.Sparse.eval_collectBalanced, rawRowCheck17195]

def rawRow17196 : Integer.Sparse Key := [(key1982, -2), (key1977, -2), (key1974, -2), (key1982, 6), (key1982, -2), (key1977, -2), (key1974, -2), (key2223, 2), (key2214, 2), (key2219, 2), (key1977, 2), (key2210, 2), (key1974, 2), (key2223, -2), (key2219, -2), (key1982, -2), (key1982, 6), (key2223, -2), (key2219, -2), (key1982, -2)]

theorem rawRowCheck17196 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form8 = rawRow17196 := by decide +kernel

def row17196 : Integer.Sparse Key := [(key1974, -2), (key1977, -2), (key1982, 4), (key2210, 2), (key2214, 2), (key2219, -2), (key2223, -2)]

theorem rowCheck17196 : row17196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17196 := by decide +kernel

theorem rowEval17196 (x : Key → ℝ) : Integer.Sparse.eval row17196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17196, Integer.Sparse.eval_collectBalanced, rawRowCheck17196]

def rawRow17197 : Integer.Sparse Key := [(key1974, -2), (key1982, -2), (key1982, -2), (key1977, 6), (key2210, -2), (key2219, -2), (key2219, -2), (key1974, 2), (key1982, 2), (key1974, 2), (key2223, 2), (key1982, 2), (key2223, 2), (key1977, -2), (key1977, -2), (key2214, -2), (key2219, 6), (key1982, -2), (key1982, -2), (key2223, -2)]

theorem rawRowCheck17197 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form8 = rawRow17197 := by decide +kernel

def row17197 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

theorem rowCheck17197 : row17197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17197 := by decide +kernel

theorem rowEval17197 (x : Key → ℝ) : Integer.Sparse.eval row17197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck17197, Integer.Sparse.eval_collectBalanced, rawRowCheck17197]

def rawRow17198 : Integer.Sparse Key := [(key1982, -2), (key1974, -2), (key1982, -2), (key1977, 6), (key2219, -2), (key2210, -2), (key2219, -2), (key1982, 2), (key1974, 2), (key2223, 2), (key1974, 2), (key2223, 2), (key1982, 2), (key1977, -2), (key2214, -2), (key1977, -2), (key2219, 6), (key1982, -2), (key2223, -2), (key1982, -2)]

theorem rawRowCheck17198 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form8 = rawRow17198 := by decide +kernel

def row17198 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

theorem rowCheck17198 : row17198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17198 := by decide +kernel

theorem rowEval17198 (x : Key → ℝ) : Integer.Sparse.eval row17198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17198, Integer.Sparse.eval_collectBalanced, rawRowCheck17198]

def rawRow17199 : Integer.Sparse Key := [(key1982, -2), (key1982, -2), (key1974, -2), (key1977, 6), (key2219, -2), (key2219, -2), (key2210, -2), (key2223, 2), (key2223, 2), (key1982, 2), (key1982, 2), (key1974, 2), (key1974, 2), (key2214, -2), (key1977, -2), (key1977, -2), (key2219, 6), (key2223, -2), (key1982, -2), (key1982, -2)]

theorem rawRowCheck17199 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form8 = rawRow17199 := by decide +kernel

def row17199 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

theorem rowCheck17199 : row17199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17199 := by decide +kernel

theorem rowEval17199 (x : Key → ℝ) : Integer.Sparse.eval row17199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17199, Integer.Sparse.eval_collectBalanced, rawRowCheck17199]

def rawRow17200 : Integer.Sparse Key := [(key1977, -2), (key1982, -2), (key1982, -2), (key1974, 6), (key2214, -2), (key2223, -2), (key2223, -2), (key1977, 2), (key1982, 2), (key1977, 2), (key2219, 2), (key1982, 2), (key2219, 2), (key1974, -2), (key1974, -2), (key2210, -2), (key2223, 6), (key1982, -2), (key1982, -2), (key2219, -2)]

theorem rawRowCheck17200 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form8 = rawRow17200 := by decide +kernel

def row17200 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

theorem rowCheck17200 : row17200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17200 := by decide +kernel

theorem rowEval17200 (x : Key → ℝ) : Integer.Sparse.eval row17200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17200, Integer.Sparse.eval_collectBalanced, rawRowCheck17200]

def rawRow17201 : Integer.Sparse Key := [(key1982, -2), (key1977, -2), (key1982, -2), (key1974, 6), (key2223, -2), (key2214, -2), (key2223, -2), (key1982, 2), (key1977, 2), (key2219, 2), (key1977, 2), (key2219, 2), (key1982, 2), (key1974, -2), (key2210, -2), (key1974, -2), (key2223, 6), (key1982, -2), (key2219, -2), (key1982, -2)]

theorem rawRowCheck17201 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form8 = rawRow17201 := by decide +kernel

def row17201 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

theorem rowCheck17201 : row17201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17201 := by decide +kernel

theorem rowEval17201 (x : Key → ℝ) : Integer.Sparse.eval row17201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17201, Integer.Sparse.eval_collectBalanced, rawRowCheck17201]

def rawRow17202 : Integer.Sparse Key := [(key1982, -2), (key1982, -2), (key1977, -2), (key1974, 6), (key2223, -2), (key2223, -2), (key2214, -2), (key2219, 2), (key2219, 2), (key1982, 2), (key1982, 2), (key1977, 2), (key1977, 2), (key2210, -2), (key1974, -2), (key1974, -2), (key2223, 6), (key2219, -2), (key1982, -2), (key1982, -2)]

theorem rawRowCheck17202 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form8 = rawRow17202 := by decide +kernel

def row17202 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

theorem rowCheck17202 : row17202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17202 := by decide +kernel

theorem rowEval17202 (x : Key → ℝ) : Integer.Sparse.eval row17202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17202, Integer.Sparse.eval_collectBalanced, rawRowCheck17202]

def rawRow17203 : Integer.Sparse Key := [(key2210, -2), (key2219, -2), (key2219, -2), (key2219, 6), (key1974, -2), (key1982, -2), (key1982, -2), (key1974, 2), (key1982, 2), (key1974, 2), (key2223, 2), (key1982, 2), (key2223, 2), (key1982, -2), (key1982, -2), (key2223, -2), (key1977, 6), (key1977, -2), (key1977, -2), (key2214, -2)]

theorem rawRowCheck17203 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form8 = rawRow17203 := by decide +kernel

def row17203 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

theorem rowCheck17203 : row17203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17203 := by decide +kernel

theorem rowEval17203 (x : Key → ℝ) : Integer.Sparse.eval row17203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form8) x := by
  rw [rowCheck17203, Integer.Sparse.eval_collectBalanced, rawRowCheck17203]

def rawRow17204 : Integer.Sparse Key := [(key2219, -2), (key2210, -2), (key2219, -2), (key2219, 6), (key1982, -2), (key1974, -2), (key1982, -2), (key1982, 2), (key1974, 2), (key2223, 2), (key1974, 2), (key2223, 2), (key1982, 2), (key1982, -2), (key2223, -2), (key1982, -2), (key1977, 6), (key1977, -2), (key2214, -2), (key1977, -2)]

theorem rawRowCheck17204 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form8 = rawRow17204 := by decide +kernel

def row17204 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

theorem rowCheck17204 : row17204 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17204 := by decide +kernel

theorem rowEval17204 (x : Key → ℝ) : Integer.Sparse.eval row17204 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17204, Integer.Sparse.eval_collectBalanced, rawRowCheck17204]

def rawRow17205 : Integer.Sparse Key := [(key2219, -2), (key2219, -2), (key2210, -2), (key2219, 6), (key1982, -2), (key1982, -2), (key1974, -2), (key2223, 2), (key2223, 2), (key1982, 2), (key1982, 2), (key1974, 2), (key1974, 2), (key2223, -2), (key1982, -2), (key1982, -2), (key1977, 6), (key2214, -2), (key1977, -2), (key1977, -2)]

theorem rawRowCheck17205 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form8 = rawRow17205 := by decide +kernel

def row17205 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

theorem rowCheck17205 : row17205 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17205 := by decide +kernel

theorem rowEval17205 (x : Key → ℝ) : Integer.Sparse.eval row17205 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17205, Integer.Sparse.eval_collectBalanced, rawRowCheck17205]

def rawRow17206 : Integer.Sparse Key := [(key2219, -2), (key2219, -2), (key2219, -2), (key2210, 6), (key2223, -2), (key2223, -2), (key2223, -2), (key1982, 2), (key1982, 2), (key1982, 2), (key1982, 2), (key1982, 2), (key1982, 2), (key1974, -2), (key1974, -2), (key1974, -2), (key2214, 6), (key1977, -2), (key1977, -2), (key1977, -2)]

theorem rawRowCheck17206 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form8 = rawRow17206 := by decide +kernel

def row17206 : Integer.Sparse Key := [(key1974, -6), (key1977, -6), (key1982, 12), (key2210, 6), (key2214, 6), (key2219, -6), (key2223, -6)]

theorem rowCheck17206 : row17206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17206 := by decide +kernel

theorem rowEval17206 (x : Key → ℝ) : Integer.Sparse.eval row17206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17206, Integer.Sparse.eval_collectBalanced, rawRowCheck17206]

def rawRow17207 : Integer.Sparse Key := [(key2214, -2), (key2223, -2), (key2223, -2), (key2223, 6), (key1977, -2), (key1982, -2), (key1982, -2), (key1977, 2), (key1982, 2), (key1977, 2), (key2219, 2), (key1982, 2), (key2219, 2), (key1982, -2), (key1982, -2), (key2219, -2), (key1974, 6), (key1974, -2), (key1974, -2), (key2210, -2)]

theorem rawRowCheck17207 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form8 = rawRow17207 := by decide +kernel

def row17207 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

theorem rowCheck17207 : row17207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17207 := by decide +kernel

theorem rowEval17207 (x : Key → ℝ) : Integer.Sparse.eval row17207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck17207, Integer.Sparse.eval_collectBalanced, rawRowCheck17207]

def rawRow17208 : Integer.Sparse Key := [(key2223, -2), (key2214, -2), (key2223, -2), (key2223, 6), (key1982, -2), (key1977, -2), (key1982, -2), (key1982, 2), (key1977, 2), (key2219, 2), (key1977, 2), (key2219, 2), (key1982, 2), (key1982, -2), (key2219, -2), (key1982, -2), (key1974, 6), (key1974, -2), (key2210, -2), (key1974, -2)]

theorem rawRowCheck17208 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form8 = rawRow17208 := by decide +kernel

def row17208 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

theorem rowCheck17208 : row17208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17208 := by decide +kernel

theorem rowEval17208 (x : Key → ℝ) : Integer.Sparse.eval row17208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17208, Integer.Sparse.eval_collectBalanced, rawRowCheck17208]

def rawRow17209 : Integer.Sparse Key := [(key2223, -2), (key2223, -2), (key2214, -2), (key2223, 6), (key1982, -2), (key1982, -2), (key1977, -2), (key2219, 2), (key2219, 2), (key1982, 2), (key1982, 2), (key1977, 2), (key1977, 2), (key2219, -2), (key1982, -2), (key1982, -2), (key1974, 6), (key2210, -2), (key1974, -2), (key1974, -2)]

theorem rawRowCheck17209 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form8 = rawRow17209 := by decide +kernel

def row17209 : Integer.Sparse Key := [(key1974, 2), (key1977, 2), (key1982, -4), (key2210, -2), (key2214, -2), (key2219, 2), (key2223, 2)]

theorem rowCheck17209 : row17209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17209 := by decide +kernel

theorem rowEval17209 (x : Key → ℝ) : Integer.Sparse.eval row17209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17209, Integer.Sparse.eval_collectBalanced, rawRowCheck17209]

def rawRow17210 : Integer.Sparse Key := [(key2223, -2), (key2223, -2), (key2223, -2), (key2214, 6), (key2219, -2), (key2219, -2), (key2219, -2), (key1982, 2), (key1982, 2), (key1982, 2), (key1982, 2), (key1982, 2), (key1982, 2), (key1977, -2), (key1977, -2), (key1977, -2), (key2210, 6), (key1974, -2), (key1974, -2), (key1974, -2)]

theorem rawRowCheck17210 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form8 = rawRow17210 := by decide +kernel

def row17210 : Integer.Sparse Key := [(key1974, -6), (key1977, -6), (key1982, 12), (key2210, 6), (key2214, 6), (key2219, -6), (key2223, -6)]

theorem rowCheck17210 : row17210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17210 := by decide +kernel

theorem rowEval17210 (x : Key → ℝ) : Integer.Sparse.eval row17210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck17210, Integer.Sparse.eval_collectBalanced, rawRowCheck17210]

def rawRow17211 : Integer.Sparse Key := [(key758, 4), (key762, 4), (key764, 4), (key762, -4), (key764, -4), (key789, -4), (key762, -4), (key764, -4), (key789, -4), (key789, 12)]

theorem rawRowCheck17211 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form9 = rawRow17211 := by decide +kernel

def row17211 : Integer.Sparse Key := [(key758, 4), (key762, -4), (key764, -4), (key789, 4)]

theorem rowCheck17211 : row17211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17211 := by decide +kernel

theorem rowEval17211 (x : Key → ℝ) : Integer.Sparse.eval row17211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck17211, Integer.Sparse.eval_collectBalanced, rawRowCheck17211]

def rawRow17212 : Integer.Sparse Key := [(key758, 4), (key764, 4), (key762, 4), (key764, -4), (key762, -4), (key789, -4), (key764, -4), (key762, -4), (key789, -4), (key789, 12)]

theorem rawRowCheck17212 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form9 = rawRow17212 := by decide +kernel

def row17212 : Integer.Sparse Key := [(key758, 4), (key762, -4), (key764, -4), (key789, 4)]

theorem rowCheck17212 : row17212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17212 := by decide +kernel

theorem rowEval17212 (x : Key → ℝ) : Integer.Sparse.eval row17212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17212, Integer.Sparse.eval_collectBalanced, rawRowCheck17212]

def rawRow17213 : Integer.Sparse Key := [(key762, 4), (key758, 4), (key764, 4), (key762, -4), (key789, -4), (key764, -4), (key762, -4), (key789, -4), (key764, -4), (key789, 12)]

theorem rawRowCheck17213 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form9 = rawRow17213 := by decide +kernel

def row17213 : Integer.Sparse Key := [(key758, 4), (key762, -4), (key764, -4), (key789, 4)]

theorem rowCheck17213 : row17213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17213 := by decide +kernel

theorem rowEval17213 (x : Key → ℝ) : Integer.Sparse.eval row17213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck17213, Integer.Sparse.eval_collectBalanced, rawRowCheck17213]

def rawRow17214 : Integer.Sparse Key := [(key762, 4), (key764, 4), (key758, 4), (key789, -4), (key762, -4), (key764, -4), (key789, -4), (key762, -4), (key764, -4), (key789, 12)]

theorem rawRowCheck17214 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form9 = rawRow17214 := by decide +kernel

def row17214 : Integer.Sparse Key := [(key758, 4), (key762, -4), (key764, -4), (key789, 4)]

theorem rowCheck17214 : row17214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17214 := by decide +kernel

theorem rowEval17214 (x : Key → ℝ) : Integer.Sparse.eval row17214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17214, Integer.Sparse.eval_collectBalanced, rawRowCheck17214]

def rawRow17215 : Integer.Sparse Key := [(key764, 4), (key758, 4), (key762, 4), (key764, -4), (key789, -4), (key762, -4), (key764, -4), (key789, -4), (key762, -4), (key789, 12)]

theorem rawRowCheck17215 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form9 = rawRow17215 := by decide +kernel

def row17215 : Integer.Sparse Key := [(key758, 4), (key762, -4), (key764, -4), (key789, 4)]

theorem rowCheck17215 : row17215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17215 := by decide +kernel

theorem rowEval17215 (x : Key → ℝ) : Integer.Sparse.eval row17215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17215, Integer.Sparse.eval_collectBalanced, rawRowCheck17215]

def rawRow17216 : Integer.Sparse Key := [(key764, 4), (key762, 4), (key758, 4), (key789, -4), (key764, -4), (key762, -4), (key789, -4), (key764, -4), (key762, -4), (key789, 12)]

theorem rawRowCheck17216 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form9 = rawRow17216 := by decide +kernel

def row17216 : Integer.Sparse Key := [(key758, 4), (key762, -4), (key764, -4), (key789, 4)]

theorem rowCheck17216 : row17216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17216 := by decide +kernel

theorem rowEval17216 (x : Key → ℝ) : Integer.Sparse.eval row17216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17216, Integer.Sparse.eval_collectBalanced, rawRowCheck17216]

def rawRow17217 : Integer.Sparse Key := [(key762, 4), (key762, 4), (key789, 4), (key758, -4), (key764, -4), (key764, -4), (key762, -4), (key789, -4), (key789, -4), (key764, 12)]

theorem rawRowCheck17217 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form9 = rawRow17217 := by decide +kernel

def row17217 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

theorem rowCheck17217 : row17217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17217 := by decide +kernel

theorem rowEval17217 (x : Key → ℝ) : Integer.Sparse.eval row17217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck17217, Integer.Sparse.eval_collectBalanced, rawRowCheck17217]

def rawRow17218 : Integer.Sparse Key := [(key762, 4), (key789, 4), (key762, 4), (key764, -4), (key758, -4), (key764, -4), (key789, -4), (key762, -4), (key789, -4), (key764, 12)]

theorem rawRowCheck17218 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form9 = rawRow17218 := by decide +kernel

def row17218 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

theorem rowCheck17218 : row17218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17218 := by decide +kernel

theorem rowEval17218 (x : Key → ℝ) : Integer.Sparse.eval row17218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17218, Integer.Sparse.eval_collectBalanced, rawRowCheck17218]

def rawRow17219 : Integer.Sparse Key := [(key789, 4), (key762, 4), (key762, 4), (key764, -4), (key764, -4), (key758, -4), (key789, -4), (key789, -4), (key762, -4), (key764, 12)]

theorem rawRowCheck17219 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form9 = rawRow17219 := by decide +kernel

def row17219 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

theorem rowCheck17219 : row17219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17219 := by decide +kernel

theorem rowEval17219 (x : Key → ℝ) : Integer.Sparse.eval row17219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17219, Integer.Sparse.eval_collectBalanced, rawRowCheck17219]

def rawRow17220 : Integer.Sparse Key := [(key764, 4), (key764, 4), (key789, 4), (key758, -4), (key762, -4), (key762, -4), (key764, -4), (key789, -4), (key789, -4), (key762, 12)]

theorem rawRowCheck17220 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form9 = rawRow17220 := by decide +kernel

def row17220 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

theorem rowCheck17220 : row17220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17220 := by decide +kernel

theorem rowEval17220 (x : Key → ℝ) : Integer.Sparse.eval row17220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17220, Integer.Sparse.eval_collectBalanced, rawRowCheck17220]

def rawRow17221 : Integer.Sparse Key := [(key764, 4), (key789, 4), (key764, 4), (key762, -4), (key758, -4), (key762, -4), (key789, -4), (key764, -4), (key789, -4), (key762, 12)]

theorem rawRowCheck17221 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form9 = rawRow17221 := by decide +kernel

def row17221 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

theorem rowCheck17221 : row17221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17221 := by decide +kernel

theorem rowEval17221 (x : Key → ℝ) : Integer.Sparse.eval row17221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17221, Integer.Sparse.eval_collectBalanced, rawRowCheck17221]

def rawRow17222 : Integer.Sparse Key := [(key789, 4), (key764, 4), (key764, 4), (key762, -4), (key762, -4), (key758, -4), (key789, -4), (key789, -4), (key764, -4), (key762, 12)]

theorem rawRowCheck17222 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form9 = rawRow17222 := by decide +kernel

def row17222 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

theorem rowCheck17222 : row17222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17222 := by decide +kernel

theorem rowEval17222 (x : Key → ℝ) : Integer.Sparse.eval row17222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17222, Integer.Sparse.eval_collectBalanced, rawRowCheck17222]

def rawRow17223 : Integer.Sparse Key := [(key762, 4), (key762, 4), (key789, 4), (key762, -4), (key789, -4), (key789, -4), (key758, -4), (key764, -4), (key764, -4), (key764, 12)]

theorem rawRowCheck17223 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form9 = rawRow17223 := by decide +kernel

def row17223 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

theorem rowCheck17223 : row17223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17223 := by decide +kernel

theorem rowEval17223 (x : Key → ℝ) : Integer.Sparse.eval row17223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form9) x := by
  rw [rowCheck17223, Integer.Sparse.eval_collectBalanced, rawRowCheck17223]

def rawRow17224 : Integer.Sparse Key := [(key762, 4), (key789, 4), (key762, 4), (key789, -4), (key762, -4), (key789, -4), (key764, -4), (key758, -4), (key764, -4), (key764, 12)]

theorem rawRowCheck17224 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form9 = rawRow17224 := by decide +kernel

def row17224 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

theorem rowCheck17224 : row17224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17224 := by decide +kernel

theorem rowEval17224 (x : Key → ℝ) : Integer.Sparse.eval row17224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17224, Integer.Sparse.eval_collectBalanced, rawRowCheck17224]

def rawRow17225 : Integer.Sparse Key := [(key789, 4), (key762, 4), (key762, 4), (key789, -4), (key789, -4), (key762, -4), (key764, -4), (key764, -4), (key758, -4), (key764, 12)]

theorem rawRowCheck17225 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form9 = rawRow17225 := by decide +kernel

def row17225 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

theorem rowCheck17225 : row17225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17225 := by decide +kernel

theorem rowEval17225 (x : Key → ℝ) : Integer.Sparse.eval row17225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17225, Integer.Sparse.eval_collectBalanced, rawRowCheck17225]

def rawRow17226 : Integer.Sparse Key := [(key789, 4), (key789, 4), (key789, 4), (key762, -4), (key762, -4), (key762, -4), (key764, -4), (key764, -4), (key764, -4), (key758, 12)]

theorem rawRowCheck17226 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form9 = rawRow17226 := by decide +kernel

def row17226 : Integer.Sparse Key := [(key758, 12), (key762, -12), (key764, -12), (key789, 12)]

theorem rowCheck17226 : row17226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17226 := by decide +kernel

theorem rowEval17226 (x : Key → ℝ) : Integer.Sparse.eval row17226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17226, Integer.Sparse.eval_collectBalanced, rawRowCheck17226]

def rawRow17227 : Integer.Sparse Key := [(key764, 4), (key764, 4), (key789, 4), (key764, -4), (key789, -4), (key789, -4), (key758, -4), (key762, -4), (key762, -4), (key762, 12)]

theorem rawRowCheck17227 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form9 = rawRow17227 := by decide +kernel

def row17227 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

theorem rowCheck17227 : row17227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17227 := by decide +kernel

theorem rowEval17227 (x : Key → ℝ) : Integer.Sparse.eval row17227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck17227, Integer.Sparse.eval_collectBalanced, rawRowCheck17227]

def rawRow17228 : Integer.Sparse Key := [(key764, 4), (key789, 4), (key764, 4), (key789, -4), (key764, -4), (key789, -4), (key762, -4), (key758, -4), (key762, -4), (key762, 12)]

theorem rawRowCheck17228 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form9 = rawRow17228 := by decide +kernel

def row17228 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

theorem rowCheck17228 : row17228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17228 := by decide +kernel

theorem rowEval17228 (x : Key → ℝ) : Integer.Sparse.eval row17228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17228, Integer.Sparse.eval_collectBalanced, rawRowCheck17228]

def rawRow17229 : Integer.Sparse Key := [(key789, 4), (key764, 4), (key764, 4), (key789, -4), (key789, -4), (key764, -4), (key762, -4), (key762, -4), (key758, -4), (key762, 12)]

theorem rawRowCheck17229 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form9 = rawRow17229 := by decide +kernel

def row17229 : Integer.Sparse Key := [(key758, -4), (key762, 4), (key764, 4), (key789, -4)]

theorem rowCheck17229 : row17229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17229 := by decide +kernel

theorem rowEval17229 (x : Key → ℝ) : Integer.Sparse.eval row17229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17229, Integer.Sparse.eval_collectBalanced, rawRowCheck17229]

def rawRow17230 : Integer.Sparse Key := [(key789, 4), (key789, 4), (key789, 4), (key764, -4), (key764, -4), (key764, -4), (key762, -4), (key762, -4), (key762, -4), (key758, 12)]

theorem rawRowCheck17230 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form9 = rawRow17230 := by decide +kernel

def row17230 : Integer.Sparse Key := [(key758, 12), (key762, -12), (key764, -12), (key789, 12)]

theorem rowCheck17230 : row17230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17230 := by decide +kernel

theorem rowEval17230 (x : Key → ℝ) : Integer.Sparse.eval row17230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17230, Integer.Sparse.eval_collectBalanced, rawRowCheck17230]

def rawRow17231 : Integer.Sparse Key := [(key2014, -1), (key2018, -1), (key2128, -1), (key2133, -1), (key2138, -1), (key2141, -1), (key2023, 2), (key2138, 2), (key2141, 2), (key2014, -1), (key2018, -1), (key2128, -1), (key2133, -1), (key2138, -1), (key2141, -1), (key2043, 2), (key2046, 2), (key2128, 2), (key2133, 2), (key2221, 2), (key2222, 2), (key2051, -1), (key2052, -1), (key2138, -1), (key2141, -1), (key2221, -1), (key2222, -1), (key2023, 2), (key2138, 2), (key2141, 2), (key2051, -1), (key2052, -1), (key2138, -1), (key2141, -1), (key2221, -1), (key2222, -1)]

theorem rawRowCheck17231 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form10 = rawRow17231 := by decide +kernel

def row17231 : Integer.Sparse Key := [(key2014, -2), (key2018, -2), (key2023, 4), (key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2)]

theorem rowCheck17231 : row17231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17231 := by decide +kernel

theorem rowEval17231 (x : Key → ℝ) : Integer.Sparse.eval row17231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck17231, Integer.Sparse.eval_collectBalanced, rawRowCheck17231]

def rawRow17232 : Integer.Sparse Key := [(key2018, -1), (key2014, -1), (key2133, -1), (key2128, -1), (key2141, -1), (key2138, -1), (key2023, 2), (key2141, 2), (key2138, 2), (key2018, -1), (key2014, -1), (key2133, -1), (key2128, -1), (key2141, -1), (key2138, -1), (key2046, 2), (key2043, 2), (key2133, 2), (key2128, 2), (key2222, 2), (key2221, 2), (key2052, -1), (key2051, -1), (key2141, -1), (key2138, -1), (key2222, -1), (key2221, -1), (key2023, 2), (key2141, 2), (key2138, 2), (key2052, -1), (key2051, -1), (key2141, -1), (key2138, -1), (key2222, -1), (key2221, -1)]

theorem rawRowCheck17232 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form10 = rawRow17232 := by decide +kernel

def row17232 : Integer.Sparse Key := [(key2014, -2), (key2018, -2), (key2023, 4), (key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2)]

theorem rowCheck17232 : row17232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17232 := by decide +kernel

theorem rowEval17232 (x : Key → ℝ) : Integer.Sparse.eval row17232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17232, Integer.Sparse.eval_collectBalanced, rawRowCheck17232]

def rawRow17233 : Integer.Sparse Key := [(key2128, -1), (key2138, -1), (key2014, -1), (key2141, -1), (key2018, -1), (key2133, -1), (key2138, 2), (key2023, 2), (key2141, 2), (key2128, -1), (key2138, -1), (key2014, -1), (key2141, -1), (key2018, -1), (key2133, -1), (key2128, 2), (key2221, 2), (key2043, 2), (key2222, 2), (key2046, 2), (key2133, 2), (key2138, -1), (key2221, -1), (key2051, -1), (key2222, -1), (key2052, -1), (key2141, -1), (key2138, 2), (key2023, 2), (key2141, 2), (key2138, -1), (key2221, -1), (key2051, -1), (key2222, -1), (key2052, -1), (key2141, -1)]

theorem rawRowCheck17233 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form10 = rawRow17233 := by decide +kernel

def row17233 : Integer.Sparse Key := [(key2014, -2), (key2018, -2), (key2023, 4), (key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2)]

theorem rowCheck17233 : row17233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17233 := by decide +kernel

theorem rowEval17233 (x : Key → ℝ) : Integer.Sparse.eval row17233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck17233, Integer.Sparse.eval_collectBalanced, rawRowCheck17233]

def rawRow17234 : Integer.Sparse Key := [(key2138, -1), (key2128, -1), (key2141, -1), (key2014, -1), (key2133, -1), (key2018, -1), (key2138, 2), (key2141, 2), (key2023, 2), (key2138, -1), (key2128, -1), (key2141, -1), (key2014, -1), (key2133, -1), (key2018, -1), (key2221, 2), (key2128, 2), (key2222, 2), (key2043, 2), (key2133, 2), (key2046, 2), (key2221, -1), (key2138, -1), (key2222, -1), (key2051, -1), (key2141, -1), (key2052, -1), (key2138, 2), (key2141, 2), (key2023, 2), (key2221, -1), (key2138, -1), (key2222, -1), (key2051, -1), (key2141, -1), (key2052, -1)]

theorem rawRowCheck17234 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form10 = rawRow17234 := by decide +kernel

def row17234 : Integer.Sparse Key := [(key2014, -2), (key2018, -2), (key2023, 4), (key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2)]

theorem rowCheck17234 : row17234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17234 := by decide +kernel

theorem rowEval17234 (x : Key → ℝ) : Integer.Sparse.eval row17234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17234, Integer.Sparse.eval_collectBalanced, rawRowCheck17234]

def rawRow17235 : Integer.Sparse Key := [(key2133, -1), (key2141, -1), (key2018, -1), (key2138, -1), (key2014, -1), (key2128, -1), (key2141, 2), (key2023, 2), (key2138, 2), (key2133, -1), (key2141, -1), (key2018, -1), (key2138, -1), (key2014, -1), (key2128, -1), (key2133, 2), (key2222, 2), (key2046, 2), (key2221, 2), (key2043, 2), (key2128, 2), (key2141, -1), (key2222, -1), (key2052, -1), (key2221, -1), (key2051, -1), (key2138, -1), (key2141, 2), (key2023, 2), (key2138, 2), (key2141, -1), (key2222, -1), (key2052, -1), (key2221, -1), (key2051, -1), (key2138, -1)]

theorem rawRowCheck17235 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form10 = rawRow17235 := by decide +kernel

def row17235 : Integer.Sparse Key := [(key2014, -2), (key2018, -2), (key2023, 4), (key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2)]

theorem rowCheck17235 : row17235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17235 := by decide +kernel

theorem rowEval17235 (x : Key → ℝ) : Integer.Sparse.eval row17235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17235, Integer.Sparse.eval_collectBalanced, rawRowCheck17235]

def rawRow17236 : Integer.Sparse Key := [(key2141, -1), (key2133, -1), (key2138, -1), (key2018, -1), (key2128, -1), (key2014, -1), (key2141, 2), (key2138, 2), (key2023, 2), (key2141, -1), (key2133, -1), (key2138, -1), (key2018, -1), (key2128, -1), (key2014, -1), (key2222, 2), (key2133, 2), (key2221, 2), (key2046, 2), (key2128, 2), (key2043, 2), (key2222, -1), (key2141, -1), (key2221, -1), (key2052, -1), (key2138, -1), (key2051, -1), (key2141, 2), (key2138, 2), (key2023, 2), (key2222, -1), (key2141, -1), (key2221, -1), (key2052, -1), (key2138, -1), (key2051, -1)]

theorem rawRowCheck17236 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form10 = rawRow17236 := by decide +kernel

def row17236 : Integer.Sparse Key := [(key2014, -2), (key2018, -2), (key2023, 4), (key2043, 2), (key2046, 2), (key2051, -2), (key2052, -2)]

theorem rowCheck17236 : row17236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17236 := by decide +kernel

theorem rowEval17236 (x : Key → ℝ) : Integer.Sparse.eval row17236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17236, Integer.Sparse.eval_collectBalanced, rawRowCheck17236]

def rawRow17237 : Integer.Sparse Key := [(key2014, -1), (key2023, -1), (key2014, -1), (key2141, -1), (key2023, -1), (key2141, -1), (key2018, 2), (key2018, 2), (key2133, 2), (key2043, -1), (key2051, -1), (key2043, -1), (key2222, -1), (key2051, -1), (key2222, -1), (key2014, 2), (key2052, 2), (key2014, 2), (key2141, 2), (key2052, 2), (key2141, 2), (key2018, -1), (key2046, -1), (key2018, -1), (key2133, -1), (key2046, -1), (key2133, -1), (key2051, 2), (key2051, 2), (key2222, 2), (key2023, -1), (key2052, -1), (key2023, -1), (key2141, -1), (key2052, -1), (key2141, -1)]

theorem rawRowCheck17237 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form10 = rawRow17237 := by decide +kernel

def row17237 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

theorem rowCheck17237 : row17237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17237 := by decide +kernel

theorem rowEval17237 (x : Key → ℝ) : Integer.Sparse.eval row17237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck17237, Integer.Sparse.eval_collectBalanced, rawRowCheck17237]

def rawRow17238 : Integer.Sparse Key := [(key2023, -1), (key2014, -1), (key2141, -1), (key2014, -1), (key2141, -1), (key2023, -1), (key2018, 2), (key2133, 2), (key2018, 2), (key2051, -1), (key2043, -1), (key2222, -1), (key2043, -1), (key2222, -1), (key2051, -1), (key2052, 2), (key2014, 2), (key2141, 2), (key2014, 2), (key2141, 2), (key2052, 2), (key2046, -1), (key2018, -1), (key2133, -1), (key2018, -1), (key2133, -1), (key2046, -1), (key2051, 2), (key2222, 2), (key2051, 2), (key2052, -1), (key2023, -1), (key2141, -1), (key2023, -1), (key2141, -1), (key2052, -1)]

theorem rawRowCheck17238 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form10 = rawRow17238 := by decide +kernel

def row17238 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

theorem rowCheck17238 : row17238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17238 := by decide +kernel

theorem rowEval17238 (x : Key → ℝ) : Integer.Sparse.eval row17238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17238, Integer.Sparse.eval_collectBalanced, rawRowCheck17238]

def rawRow17239 : Integer.Sparse Key := [(key2141, -1), (key2141, -1), (key2023, -1), (key2023, -1), (key2014, -1), (key2014, -1), (key2133, 2), (key2018, 2), (key2018, 2), (key2222, -1), (key2222, -1), (key2051, -1), (key2051, -1), (key2043, -1), (key2043, -1), (key2141, 2), (key2141, 2), (key2052, 2), (key2052, 2), (key2014, 2), (key2014, 2), (key2133, -1), (key2133, -1), (key2046, -1), (key2046, -1), (key2018, -1), (key2018, -1), (key2222, 2), (key2051, 2), (key2051, 2), (key2141, -1), (key2141, -1), (key2052, -1), (key2052, -1), (key2023, -1), (key2023, -1)]

theorem rawRowCheck17239 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form10 = rawRow17239 := by decide +kernel

def row17239 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

theorem rowCheck17239 : row17239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17239 := by decide +kernel

theorem rowEval17239 (x : Key → ℝ) : Integer.Sparse.eval row17239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17239, Integer.Sparse.eval_collectBalanced, rawRowCheck17239]

def rawRow17240 : Integer.Sparse Key := [(key2018, -1), (key2023, -1), (key2018, -1), (key2138, -1), (key2023, -1), (key2138, -1), (key2014, 2), (key2014, 2), (key2128, 2), (key2046, -1), (key2052, -1), (key2046, -1), (key2221, -1), (key2052, -1), (key2221, -1), (key2018, 2), (key2051, 2), (key2018, 2), (key2138, 2), (key2051, 2), (key2138, 2), (key2014, -1), (key2043, -1), (key2014, -1), (key2128, -1), (key2043, -1), (key2128, -1), (key2052, 2), (key2052, 2), (key2221, 2), (key2023, -1), (key2051, -1), (key2023, -1), (key2138, -1), (key2051, -1), (key2138, -1)]

theorem rawRowCheck17240 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form10 = rawRow17240 := by decide +kernel

def row17240 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

theorem rowCheck17240 : row17240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17240 := by decide +kernel

theorem rowEval17240 (x : Key → ℝ) : Integer.Sparse.eval row17240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17240, Integer.Sparse.eval_collectBalanced, rawRowCheck17240]

def rawRow17241 : Integer.Sparse Key := [(key2023, -1), (key2018, -1), (key2138, -1), (key2018, -1), (key2138, -1), (key2023, -1), (key2014, 2), (key2128, 2), (key2014, 2), (key2052, -1), (key2046, -1), (key2221, -1), (key2046, -1), (key2221, -1), (key2052, -1), (key2051, 2), (key2018, 2), (key2138, 2), (key2018, 2), (key2138, 2), (key2051, 2), (key2043, -1), (key2014, -1), (key2128, -1), (key2014, -1), (key2128, -1), (key2043, -1), (key2052, 2), (key2221, 2), (key2052, 2), (key2051, -1), (key2023, -1), (key2138, -1), (key2023, -1), (key2138, -1), (key2051, -1)]

theorem rawRowCheck17241 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form10 = rawRow17241 := by decide +kernel

def row17241 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

theorem rowCheck17241 : row17241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17241 := by decide +kernel

theorem rowEval17241 (x : Key → ℝ) : Integer.Sparse.eval row17241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17241, Integer.Sparse.eval_collectBalanced, rawRowCheck17241]

def rawRow17242 : Integer.Sparse Key := [(key2138, -1), (key2138, -1), (key2023, -1), (key2023, -1), (key2018, -1), (key2018, -1), (key2128, 2), (key2014, 2), (key2014, 2), (key2221, -1), (key2221, -1), (key2052, -1), (key2052, -1), (key2046, -1), (key2046, -1), (key2138, 2), (key2138, 2), (key2051, 2), (key2051, 2), (key2018, 2), (key2018, 2), (key2128, -1), (key2128, -1), (key2043, -1), (key2043, -1), (key2014, -1), (key2014, -1), (key2221, 2), (key2052, 2), (key2052, 2), (key2138, -1), (key2138, -1), (key2051, -1), (key2051, -1), (key2023, -1), (key2023, -1)]

theorem rawRowCheck17242 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form10 = rawRow17242 := by decide +kernel

def row17242 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

theorem rowCheck17242 : row17242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17242 := by decide +kernel

theorem rowEval17242 (x : Key → ℝ) : Integer.Sparse.eval row17242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17242, Integer.Sparse.eval_collectBalanced, rawRowCheck17242]

def rawRow17243 : Integer.Sparse Key := [(key2043, -1), (key2051, -1), (key2043, -1), (key2222, -1), (key2051, -1), (key2222, -1), (key2051, 2), (key2051, 2), (key2222, 2), (key2014, -1), (key2023, -1), (key2014, -1), (key2141, -1), (key2023, -1), (key2141, -1), (key2014, 2), (key2052, 2), (key2014, 2), (key2141, 2), (key2052, 2), (key2141, 2), (key2023, -1), (key2052, -1), (key2023, -1), (key2141, -1), (key2052, -1), (key2141, -1), (key2018, 2), (key2018, 2), (key2133, 2), (key2018, -1), (key2046, -1), (key2018, -1), (key2133, -1), (key2046, -1), (key2133, -1)]

theorem rawRowCheck17243 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form10 = rawRow17243 := by decide +kernel

def row17243 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

theorem rowCheck17243 : row17243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17243 := by decide +kernel

theorem rowEval17243 (x : Key → ℝ) : Integer.Sparse.eval row17243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form10) x := by
  rw [rowCheck17243, Integer.Sparse.eval_collectBalanced, rawRowCheck17243]

def rawRow17244 : Integer.Sparse Key := [(key2051, -1), (key2043, -1), (key2222, -1), (key2043, -1), (key2222, -1), (key2051, -1), (key2051, 2), (key2222, 2), (key2051, 2), (key2023, -1), (key2014, -1), (key2141, -1), (key2014, -1), (key2141, -1), (key2023, -1), (key2052, 2), (key2014, 2), (key2141, 2), (key2014, 2), (key2141, 2), (key2052, 2), (key2052, -1), (key2023, -1), (key2141, -1), (key2023, -1), (key2141, -1), (key2052, -1), (key2018, 2), (key2133, 2), (key2018, 2), (key2046, -1), (key2018, -1), (key2133, -1), (key2018, -1), (key2133, -1), (key2046, -1)]

theorem rawRowCheck17244 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form10 = rawRow17244 := by decide +kernel

def row17244 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

theorem rowCheck17244 : row17244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17244 := by decide +kernel

theorem rowEval17244 (x : Key → ℝ) : Integer.Sparse.eval row17244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17244, Integer.Sparse.eval_collectBalanced, rawRowCheck17244]

def rawRow17245 : Integer.Sparse Key := [(key2222, -1), (key2222, -1), (key2051, -1), (key2051, -1), (key2043, -1), (key2043, -1), (key2222, 2), (key2051, 2), (key2051, 2), (key2141, -1), (key2141, -1), (key2023, -1), (key2023, -1), (key2014, -1), (key2014, -1), (key2141, 2), (key2141, 2), (key2052, 2), (key2052, 2), (key2014, 2), (key2014, 2), (key2141, -1), (key2141, -1), (key2052, -1), (key2052, -1), (key2023, -1), (key2023, -1), (key2133, 2), (key2018, 2), (key2018, 2), (key2133, -1), (key2133, -1), (key2046, -1), (key2046, -1), (key2018, -1), (key2018, -1)]

theorem rawRowCheck17245 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form10 = rawRow17245 := by decide +kernel

def row17245 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

theorem rowCheck17245 : row17245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17245 := by decide +kernel

theorem rowEval17245 (x : Key → ℝ) : Integer.Sparse.eval row17245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17245, Integer.Sparse.eval_collectBalanced, rawRowCheck17245]

def rawRow17246 : Integer.Sparse Key := [(key2051, -1), (key2051, -1), (key2051, -1), (key2051, -1), (key2051, -1), (key2051, -1), (key2043, 2), (key2043, 2), (key2043, 2), (key2052, -1), (key2052, -1), (key2052, -1), (key2052, -1), (key2052, -1), (key2052, -1), (key2023, 2), (key2023, 2), (key2023, 2), (key2023, 2), (key2023, 2), (key2023, 2), (key2014, -1), (key2014, -1), (key2014, -1), (key2014, -1), (key2014, -1), (key2014, -1), (key2046, 2), (key2046, 2), (key2046, 2), (key2018, -1), (key2018, -1), (key2018, -1), (key2018, -1), (key2018, -1), (key2018, -1)]

theorem rawRowCheck17246 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form10 = rawRow17246 := by decide +kernel

def row17246 : Integer.Sparse Key := [(key2014, -6), (key2018, -6), (key2023, 12), (key2043, 6), (key2046, 6), (key2051, -6), (key2052, -6)]

theorem rowCheck17246 : row17246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17246 := by decide +kernel

theorem rowEval17246 (x : Key → ℝ) : Integer.Sparse.eval row17246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17246, Integer.Sparse.eval_collectBalanced, rawRowCheck17246]

def rawRow17247 : Integer.Sparse Key := [(key2046, -1), (key2052, -1), (key2046, -1), (key2221, -1), (key2052, -1), (key2221, -1), (key2052, 2), (key2052, 2), (key2221, 2), (key2018, -1), (key2023, -1), (key2018, -1), (key2138, -1), (key2023, -1), (key2138, -1), (key2018, 2), (key2051, 2), (key2018, 2), (key2138, 2), (key2051, 2), (key2138, 2), (key2023, -1), (key2051, -1), (key2023, -1), (key2138, -1), (key2051, -1), (key2138, -1), (key2014, 2), (key2014, 2), (key2128, 2), (key2014, -1), (key2043, -1), (key2014, -1), (key2128, -1), (key2043, -1), (key2128, -1)]

theorem rawRowCheck17247 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form10 = rawRow17247 := by decide +kernel

def row17247 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

theorem rowCheck17247 : row17247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17247 := by decide +kernel

theorem rowEval17247 (x : Key → ℝ) : Integer.Sparse.eval row17247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck17247, Integer.Sparse.eval_collectBalanced, rawRowCheck17247]

def rawRow17248 : Integer.Sparse Key := [(key2052, -1), (key2046, -1), (key2221, -1), (key2046, -1), (key2221, -1), (key2052, -1), (key2052, 2), (key2221, 2), (key2052, 2), (key2023, -1), (key2018, -1), (key2138, -1), (key2018, -1), (key2138, -1), (key2023, -1), (key2051, 2), (key2018, 2), (key2138, 2), (key2018, 2), (key2138, 2), (key2051, 2), (key2051, -1), (key2023, -1), (key2138, -1), (key2023, -1), (key2138, -1), (key2051, -1), (key2014, 2), (key2128, 2), (key2014, 2), (key2043, -1), (key2014, -1), (key2128, -1), (key2014, -1), (key2128, -1), (key2043, -1)]

theorem rawRowCheck17248 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form10 = rawRow17248 := by decide +kernel

def row17248 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

theorem rowCheck17248 : row17248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17248 := by decide +kernel

theorem rowEval17248 (x : Key → ℝ) : Integer.Sparse.eval row17248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17248, Integer.Sparse.eval_collectBalanced, rawRowCheck17248]

def rawRow17249 : Integer.Sparse Key := [(key2221, -1), (key2221, -1), (key2052, -1), (key2052, -1), (key2046, -1), (key2046, -1), (key2221, 2), (key2052, 2), (key2052, 2), (key2138, -1), (key2138, -1), (key2023, -1), (key2023, -1), (key2018, -1), (key2018, -1), (key2138, 2), (key2138, 2), (key2051, 2), (key2051, 2), (key2018, 2), (key2018, 2), (key2138, -1), (key2138, -1), (key2051, -1), (key2051, -1), (key2023, -1), (key2023, -1), (key2128, 2), (key2014, 2), (key2014, 2), (key2128, -1), (key2128, -1), (key2043, -1), (key2043, -1), (key2014, -1), (key2014, -1)]

theorem rawRowCheck17249 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form10 = rawRow17249 := by decide +kernel

def row17249 : Integer.Sparse Key := [(key2014, 2), (key2018, 2), (key2023, -4), (key2043, -2), (key2046, -2), (key2051, 2), (key2052, 2)]

theorem rowCheck17249 : row17249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17249 := by decide +kernel

theorem rowEval17249 (x : Key → ℝ) : Integer.Sparse.eval row17249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17249, Integer.Sparse.eval_collectBalanced, rawRowCheck17249]

def rawRow17250 : Integer.Sparse Key := [(key2052, -1), (key2052, -1), (key2052, -1), (key2052, -1), (key2052, -1), (key2052, -1), (key2046, 2), (key2046, 2), (key2046, 2), (key2051, -1), (key2051, -1), (key2051, -1), (key2051, -1), (key2051, -1), (key2051, -1), (key2023, 2), (key2023, 2), (key2023, 2), (key2023, 2), (key2023, 2), (key2023, 2), (key2018, -1), (key2018, -1), (key2018, -1), (key2018, -1), (key2018, -1), (key2018, -1), (key2043, 2), (key2043, 2), (key2043, 2), (key2014, -1), (key2014, -1), (key2014, -1), (key2014, -1), (key2014, -1), (key2014, -1)]

theorem rawRowCheck17250 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form10 = rawRow17250 := by decide +kernel

def row17250 : Integer.Sparse Key := [(key2014, -6), (key2018, -6), (key2023, 12), (key2043, 6), (key2046, 6), (key2051, -6), (key2052, -6)]

theorem rowCheck17250 : row17250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17250 := by decide +kernel

theorem rowEval17250 (x : Key → ℝ) : Integer.Sparse.eval row17250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck17250, Integer.Sparse.eval_collectBalanced, rawRowCheck17250]

def rawRow17251 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, -2), (key365, 6), (key357, -2), (key359, -2), (key365, -2), (key357, 2), (key359, 2), (key527, 2), (key674, 2), (key535, 2), (key675, 2), (key365, -2), (key535, -2), (key675, -2), (key365, 6), (key365, -2), (key535, -2), (key675, -2)]

theorem rawRowCheck17251 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form11 = rawRow17251 := by decide +kernel

def row17251 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, 4), (key527, 2), (key535, -2), (key674, 2), (key675, -2)]

theorem rowCheck17251 : row17251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17251 := by decide +kernel

theorem rowEval17251 (x : Key → ℝ) : Integer.Sparse.eval row17251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck17251, Integer.Sparse.eval_collectBalanced, rawRowCheck17251]

def rawRow17252 : Integer.Sparse Key := [(key359, -2), (key357, -2), (key365, -2), (key365, 6), (key359, -2), (key357, -2), (key365, -2), (key359, 2), (key357, 2), (key674, 2), (key527, 2), (key675, 2), (key535, 2), (key365, -2), (key675, -2), (key535, -2), (key365, 6), (key365, -2), (key675, -2), (key535, -2)]

theorem rawRowCheck17252 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form11 = rawRow17252 := by decide +kernel

def row17252 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, 4), (key527, 2), (key535, -2), (key674, 2), (key675, -2)]

theorem rowCheck17252 : row17252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17252 := by decide +kernel

theorem rowEval17252 (x : Key → ℝ) : Integer.Sparse.eval row17252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17252, Integer.Sparse.eval_collectBalanced, rawRowCheck17252]

def rawRow17253 : Integer.Sparse Key := [(key357, -2), (key365, -2), (key359, -2), (key365, 6), (key357, -2), (key365, -2), (key359, -2), (key527, 2), (key535, 2), (key357, 2), (key675, 2), (key359, 2), (key674, 2), (key535, -2), (key365, -2), (key675, -2), (key365, 6), (key535, -2), (key365, -2), (key675, -2)]

theorem rawRowCheck17253 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form11 = rawRow17253 := by decide +kernel

def row17253 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, 4), (key527, 2), (key535, -2), (key674, 2), (key675, -2)]

theorem rowCheck17253 : row17253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17253 := by decide +kernel

theorem rowEval17253 (x : Key → ℝ) : Integer.Sparse.eval row17253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck17253, Integer.Sparse.eval_collectBalanced, rawRowCheck17253]

def rawRow17254 : Integer.Sparse Key := [(key365, -2), (key357, -2), (key359, -2), (key365, 6), (key365, -2), (key357, -2), (key359, -2), (key535, 2), (key527, 2), (key675, 2), (key357, 2), (key674, 2), (key359, 2), (key535, -2), (key675, -2), (key365, -2), (key365, 6), (key535, -2), (key675, -2), (key365, -2)]

theorem rawRowCheck17254 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form11 = rawRow17254 := by decide +kernel

def row17254 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, 4), (key527, 2), (key535, -2), (key674, 2), (key675, -2)]

theorem rowCheck17254 : row17254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17254 := by decide +kernel

theorem rowEval17254 (x : Key → ℝ) : Integer.Sparse.eval row17254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17254, Integer.Sparse.eval_collectBalanced, rawRowCheck17254]

def rawRow17255 : Integer.Sparse Key := [(key359, -2), (key365, -2), (key357, -2), (key365, 6), (key359, -2), (key365, -2), (key357, -2), (key674, 2), (key675, 2), (key359, 2), (key535, 2), (key357, 2), (key527, 2), (key675, -2), (key365, -2), (key535, -2), (key365, 6), (key675, -2), (key365, -2), (key535, -2)]

theorem rawRowCheck17255 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form11 = rawRow17255 := by decide +kernel

def row17255 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, 4), (key527, 2), (key535, -2), (key674, 2), (key675, -2)]

theorem rowCheck17255 : row17255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17255 := by decide +kernel

theorem rowEval17255 (x : Key → ℝ) : Integer.Sparse.eval row17255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17255, Integer.Sparse.eval_collectBalanced, rawRowCheck17255]

def rawRow17256 : Integer.Sparse Key := [(key365, -2), (key359, -2), (key357, -2), (key365, 6), (key365, -2), (key359, -2), (key357, -2), (key675, 2), (key674, 2), (key535, 2), (key359, 2), (key527, 2), (key357, 2), (key675, -2), (key535, -2), (key365, -2), (key365, 6), (key675, -2), (key535, -2), (key365, -2)]

theorem rawRowCheck17256 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form11 = rawRow17256 := by decide +kernel

def row17256 : Integer.Sparse Key := [(key357, -2), (key359, -2), (key365, 4), (key527, 2), (key535, -2), (key674, 2), (key675, -2)]

theorem rowCheck17256 : row17256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17256 := by decide +kernel

theorem rowEval17256 (x : Key → ℝ) : Integer.Sparse.eval row17256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17256, Integer.Sparse.eval_collectBalanced, rawRowCheck17256]

def rawRow17257 : Integer.Sparse Key := [(key357, -2), (key365, -2), (key365, -2), (key359, 6), (key527, -2), (key535, -2), (key535, -2), (key357, 2), (key365, 2), (key357, 2), (key675, 2), (key365, 2), (key675, 2), (key359, -2), (key359, -2), (key674, -2), (key535, 6), (key365, -2), (key365, -2), (key675, -2)]

theorem rawRowCheck17257 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form11 = rawRow17257 := by decide +kernel

def row17257 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

theorem rowCheck17257 : row17257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17257 := by decide +kernel

theorem rowEval17257 (x : Key → ℝ) : Integer.Sparse.eval row17257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck17257, Integer.Sparse.eval_collectBalanced, rawRowCheck17257]

def rawRow17258 : Integer.Sparse Key := [(key365, -2), (key357, -2), (key365, -2), (key359, 6), (key535, -2), (key527, -2), (key535, -2), (key365, 2), (key357, 2), (key675, 2), (key357, 2), (key675, 2), (key365, 2), (key359, -2), (key674, -2), (key359, -2), (key535, 6), (key365, -2), (key675, -2), (key365, -2)]

theorem rawRowCheck17258 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form11 = rawRow17258 := by decide +kernel

def row17258 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

theorem rowCheck17258 : row17258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17258 := by decide +kernel

theorem rowEval17258 (x : Key → ℝ) : Integer.Sparse.eval row17258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17258, Integer.Sparse.eval_collectBalanced, rawRowCheck17258]

def rawRow17259 : Integer.Sparse Key := [(key365, -2), (key365, -2), (key357, -2), (key359, 6), (key535, -2), (key535, -2), (key527, -2), (key675, 2), (key675, 2), (key365, 2), (key365, 2), (key357, 2), (key357, 2), (key674, -2), (key359, -2), (key359, -2), (key535, 6), (key675, -2), (key365, -2), (key365, -2)]

theorem rawRowCheck17259 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form11 = rawRow17259 := by decide +kernel

def row17259 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

theorem rowCheck17259 : row17259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17259 := by decide +kernel

theorem rowEval17259 (x : Key → ℝ) : Integer.Sparse.eval row17259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17259, Integer.Sparse.eval_collectBalanced, rawRowCheck17259]

def rawRow17260 : Integer.Sparse Key := [(key359, -2), (key365, -2), (key365, -2), (key357, 6), (key674, -2), (key675, -2), (key675, -2), (key359, 2), (key365, 2), (key359, 2), (key535, 2), (key365, 2), (key535, 2), (key357, -2), (key357, -2), (key527, -2), (key675, 6), (key365, -2), (key365, -2), (key535, -2)]

theorem rawRowCheck17260 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form11 = rawRow17260 := by decide +kernel

def row17260 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

theorem rowCheck17260 : row17260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17260 := by decide +kernel

theorem rowEval17260 (x : Key → ℝ) : Integer.Sparse.eval row17260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17260, Integer.Sparse.eval_collectBalanced, rawRowCheck17260]

def rawRow17261 : Integer.Sparse Key := [(key365, -2), (key359, -2), (key365, -2), (key357, 6), (key675, -2), (key674, -2), (key675, -2), (key365, 2), (key359, 2), (key535, 2), (key359, 2), (key535, 2), (key365, 2), (key357, -2), (key527, -2), (key357, -2), (key675, 6), (key365, -2), (key535, -2), (key365, -2)]

theorem rawRowCheck17261 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form11 = rawRow17261 := by decide +kernel

def row17261 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

theorem rowCheck17261 : row17261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17261 := by decide +kernel

theorem rowEval17261 (x : Key → ℝ) : Integer.Sparse.eval row17261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -1, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17261, Integer.Sparse.eval_collectBalanced, rawRowCheck17261]

def rawRow17262 : Integer.Sparse Key := [(key365, -2), (key365, -2), (key359, -2), (key357, 6), (key675, -2), (key675, -2), (key674, -2), (key535, 2), (key535, 2), (key365, 2), (key365, 2), (key359, 2), (key359, 2), (key527, -2), (key357, -2), (key357, -2), (key675, 6), (key535, -2), (key365, -2), (key365, -2)]

theorem rawRowCheck17262 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form11 = rawRow17262 := by decide +kernel

def row17262 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

theorem rowCheck17262 : row17262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17262 := by decide +kernel

theorem rowEval17262 (x : Key → ℝ) : Integer.Sparse.eval row17262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17262, Integer.Sparse.eval_collectBalanced, rawRowCheck17262]

def rawRow17263 : Integer.Sparse Key := [(key527, -2), (key535, -2), (key535, -2), (key535, 6), (key357, -2), (key365, -2), (key365, -2), (key357, 2), (key365, 2), (key357, 2), (key675, 2), (key365, 2), (key675, 2), (key365, -2), (key365, -2), (key675, -2), (key359, 6), (key359, -2), (key359, -2), (key674, -2)]

theorem rawRowCheck17263 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form11 = rawRow17263 := by decide +kernel

def row17263 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

theorem rowCheck17263 : row17263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17263 := by decide +kernel

theorem rowEval17263 (x : Key → ℝ) : Integer.Sparse.eval row17263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form11) x := by
  rw [rowCheck17263, Integer.Sparse.eval_collectBalanced, rawRowCheck17263]

def rawRow17264 : Integer.Sparse Key := [(key535, -2), (key527, -2), (key535, -2), (key535, 6), (key365, -2), (key357, -2), (key365, -2), (key365, 2), (key357, 2), (key675, 2), (key357, 2), (key675, 2), (key365, 2), (key365, -2), (key675, -2), (key365, -2), (key359, 6), (key359, -2), (key674, -2), (key359, -2)]

theorem rawRowCheck17264 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form11 = rawRow17264 := by decide +kernel

def row17264 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

theorem rowCheck17264 : row17264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17264 := by decide +kernel

theorem rowEval17264 (x : Key → ℝ) : Integer.Sparse.eval row17264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 2, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17264, Integer.Sparse.eval_collectBalanced, rawRowCheck17264]

def rawRow17265 : Integer.Sparse Key := [(key535, -2), (key535, -2), (key527, -2), (key535, 6), (key365, -2), (key365, -2), (key357, -2), (key675, 2), (key675, 2), (key365, 2), (key365, 2), (key357, 2), (key357, 2), (key675, -2), (key365, -2), (key365, -2), (key359, 6), (key674, -2), (key359, -2), (key359, -2)]

theorem rawRowCheck17265 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form11 = rawRow17265 := by decide +kernel

def row17265 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

theorem rowCheck17265 : row17265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17265 := by decide +kernel

theorem rowEval17265 (x : Key → ℝ) : Integer.Sparse.eval row17265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17265, Integer.Sparse.eval_collectBalanced, rawRowCheck17265]

def rawRow17266 : Integer.Sparse Key := [(key535, -2), (key535, -2), (key535, -2), (key527, 6), (key675, -2), (key675, -2), (key675, -2), (key365, 2), (key365, 2), (key365, 2), (key365, 2), (key365, 2), (key365, 2), (key357, -2), (key357, -2), (key357, -2), (key674, 6), (key359, -2), (key359, -2), (key359, -2)]

theorem rawRowCheck17266 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form11 = rawRow17266 := by decide +kernel

def row17266 : Integer.Sparse Key := [(key357, -6), (key359, -6), (key365, 12), (key527, 6), (key535, -6), (key674, 6), (key675, -6)]

theorem rowCheck17266 : row17266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17266 := by decide +kernel

theorem rowEval17266 (x : Key → ℝ) : Integer.Sparse.eval row17266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17266, Integer.Sparse.eval_collectBalanced, rawRowCheck17266]

def rawRow17267 : Integer.Sparse Key := [(key674, -2), (key675, -2), (key675, -2), (key675, 6), (key359, -2), (key365, -2), (key365, -2), (key359, 2), (key365, 2), (key359, 2), (key535, 2), (key365, 2), (key535, 2), (key365, -2), (key365, -2), (key535, -2), (key357, 6), (key357, -2), (key357, -2), (key527, -2)]

theorem rawRowCheck17267 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form11 = rawRow17267 := by decide +kernel

def row17267 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

theorem rowCheck17267 : row17267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17267 := by decide +kernel

theorem rowEval17267 (x : Key → ℝ) : Integer.Sparse.eval row17267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck17267, Integer.Sparse.eval_collectBalanced, rawRowCheck17267]

def rawRow17268 : Integer.Sparse Key := [(key675, -2), (key674, -2), (key675, -2), (key675, 6), (key365, -2), (key359, -2), (key365, -2), (key365, 2), (key359, 2), (key535, 2), (key359, 2), (key535, 2), (key365, 2), (key365, -2), (key535, -2), (key365, -2), (key357, 6), (key357, -2), (key527, -2), (key357, -2)]

theorem rawRowCheck17268 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form11 = rawRow17268 := by decide +kernel

def row17268 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

theorem rowCheck17268 : row17268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17268 := by decide +kernel

theorem rowEval17268 (x : Key → ℝ) : Integer.Sparse.eval row17268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -1, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17268, Integer.Sparse.eval_collectBalanced, rawRowCheck17268]

def rawRow17269 : Integer.Sparse Key := [(key675, -2), (key675, -2), (key674, -2), (key675, 6), (key365, -2), (key365, -2), (key359, -2), (key535, 2), (key535, 2), (key365, 2), (key365, 2), (key359, 2), (key359, 2), (key535, -2), (key365, -2), (key365, -2), (key357, 6), (key527, -2), (key357, -2), (key357, -2)]

theorem rawRowCheck17269 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form11 = rawRow17269 := by decide +kernel

def row17269 : Integer.Sparse Key := [(key357, 2), (key359, 2), (key365, -4), (key527, -2), (key535, 2), (key674, -2), (key675, 2)]

theorem rowCheck17269 : row17269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17269 := by decide +kernel

theorem rowEval17269 (x : Key → ℝ) : Integer.Sparse.eval row17269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17269, Integer.Sparse.eval_collectBalanced, rawRowCheck17269]

def rawRow17270 : Integer.Sparse Key := [(key675, -2), (key675, -2), (key675, -2), (key674, 6), (key535, -2), (key535, -2), (key535, -2), (key365, 2), (key365, 2), (key365, 2), (key365, 2), (key365, 2), (key365, 2), (key359, -2), (key359, -2), (key359, -2), (key527, 6), (key357, -2), (key357, -2), (key357, -2)]

theorem rawRowCheck17270 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form11 = rawRow17270 := by decide +kernel

def row17270 : Integer.Sparse Key := [(key357, -6), (key359, -6), (key365, 12), (key527, 6), (key535, -6), (key674, 6), (key675, -6)]

theorem rowCheck17270 : row17270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17270 := by decide +kernel

theorem rowEval17270 (x : Key → ℝ) : Integer.Sparse.eval row17270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -1, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck17270, Integer.Sparse.eval_collectBalanced, rawRowCheck17270]

def rawRow17271 : Integer.Sparse Key := [(key1976, 2), (key1981, 2), (key1983, 2), (key1981, -2), (key1983, -2), (key1997, -2), (key1976, 2), (key1981, 2), (key1983, 2), (key1981, -1), (key1983, -1), (key2218, -1), (key2224, -1), (key2262, -1), (key2266, -1), (key1981, -2), (key1983, -2), (key1997, -2), (key1981, -1), (key1983, -1), (key2218, -1), (key2224, -1), (key2262, -1), (key2266, -1), (key1997, 4), (key2262, 4), (key2266, 4)]

theorem rawRowCheck17271 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form12 = rawRow17271 := by decide +kernel

def row17271 : Integer.Sparse Key := [(key1976, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, 2), (key2266, 2)]

theorem rowCheck17271 : row17271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17271 := by decide +kernel

theorem rowEval17271 (x : Key → ℝ) : Integer.Sparse.eval row17271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 0, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck17271, Integer.Sparse.eval_collectBalanced, rawRowCheck17271]

def rawRow17272 : Integer.Sparse Key := [(key1976, 2), (key1983, 2), (key1981, 2), (key1983, -2), (key1981, -2), (key1997, -2), (key1976, 2), (key1983, 2), (key1981, 2), (key1983, -1), (key1981, -1), (key2224, -1), (key2218, -1), (key2266, -1), (key2262, -1), (key1983, -2), (key1981, -2), (key1997, -2), (key1983, -1), (key1981, -1), (key2224, -1), (key2218, -1), (key2266, -1), (key2262, -1), (key1997, 4), (key2266, 4), (key2262, 4)]

theorem rawRowCheck17272 : GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form12 = rawRow17272 := by decide +kernel

def row17272 : Integer.Sparse Key := [(key1976, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, 2), (key2266, 2)]

theorem rowCheck17272 : row17272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17272 := by decide +kernel

theorem rowEval17272 (x : Key → ℝ) : Integer.Sparse.eval row17272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17272, Integer.Sparse.eval_collectBalanced, rawRowCheck17272]

def rawRow17273 : Integer.Sparse Key := [(key1981, 2), (key1976, 2), (key1983, 2), (key1981, -2), (key1997, -2), (key1983, -2), (key1981, 2), (key1976, 2), (key1983, 2), (key2218, -1), (key2262, -1), (key1981, -1), (key2266, -1), (key1983, -1), (key2224, -1), (key1981, -2), (key1997, -2), (key1983, -2), (key2218, -1), (key2262, -1), (key1981, -1), (key2266, -1), (key1983, -1), (key2224, -1), (key2262, 4), (key1997, 4), (key2266, 4)]

theorem rawRowCheck17273 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form12 = rawRow17273 := by decide +kernel

def row17273 : Integer.Sparse Key := [(key1976, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, 2), (key2266, 2)]

theorem rowCheck17273 : row17273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17273 := by decide +kernel

theorem rowEval17273 (x : Key → ℝ) : Integer.Sparse.eval row17273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, -1, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck17273, Integer.Sparse.eval_collectBalanced, rawRowCheck17273]

def rawRow17274 : Integer.Sparse Key := [(key1981, 2), (key1983, 2), (key1976, 2), (key1997, -2), (key1981, -2), (key1983, -2), (key1981, 2), (key1983, 2), (key1976, 2), (key2262, -1), (key2218, -1), (key2266, -1), (key1981, -1), (key2224, -1), (key1983, -1), (key1997, -2), (key1981, -2), (key1983, -2), (key2262, -1), (key2218, -1), (key2266, -1), (key1981, -1), (key2224, -1), (key1983, -1), (key2262, 4), (key2266, 4), (key1997, 4)]

theorem rawRowCheck17274 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form12 = rawRow17274 := by decide +kernel

def row17274 : Integer.Sparse Key := [(key1976, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, 2), (key2266, 2)]

theorem rowCheck17274 : row17274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17274 := by decide +kernel

theorem rowEval17274 (x : Key → ℝ) : Integer.Sparse.eval row17274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 0, 2, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17274, Integer.Sparse.eval_collectBalanced, rawRowCheck17274]

def rawRow17275 : Integer.Sparse Key := [(key1983, 2), (key1976, 2), (key1981, 2), (key1983, -2), (key1997, -2), (key1981, -2), (key1983, 2), (key1976, 2), (key1981, 2), (key2224, -1), (key2266, -1), (key1983, -1), (key2262, -1), (key1981, -1), (key2218, -1), (key1983, -2), (key1997, -2), (key1981, -2), (key2224, -1), (key2266, -1), (key1983, -1), (key2262, -1), (key1981, -1), (key2218, -1), (key2266, 4), (key1997, 4), (key2262, 4)]

theorem rawRowCheck17275 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form12 = rawRow17275 := by decide +kernel

def row17275 : Integer.Sparse Key := [(key1976, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, 2), (key2266, 2)]

theorem rowCheck17275 : row17275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17275 := by decide +kernel

theorem rowEval17275 (x : Key → ℝ) : Integer.Sparse.eval row17275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17275, Integer.Sparse.eval_collectBalanced, rawRowCheck17275]

def rawRow17276 : Integer.Sparse Key := [(key1983, 2), (key1981, 2), (key1976, 2), (key1997, -2), (key1983, -2), (key1981, -2), (key1983, 2), (key1981, 2), (key1976, 2), (key2266, -1), (key2224, -1), (key2262, -1), (key1983, -1), (key2218, -1), (key1981, -1), (key1997, -2), (key1983, -2), (key1981, -2), (key2266, -1), (key2224, -1), (key2262, -1), (key1983, -1), (key2218, -1), (key1981, -1), (key2266, 4), (key2262, 4), (key1997, 4)]

theorem rawRowCheck17276 : GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form12 = rawRow17276 := by decide +kernel

def row17276 : Integer.Sparse Key := [(key1976, 4), (key1981, -2), (key1983, -2), (key2218, -2), (key2224, -2), (key2262, 2), (key2266, 2)]

theorem rowCheck17276 : row17276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17276 := by decide +kernel

theorem rowEval17276 (x : Key → ℝ) : Integer.Sparse.eval row17276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, 2, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17276, Integer.Sparse.eval_collectBalanced, rawRowCheck17276]

def rawRow17277 : Integer.Sparse Key := [(key1981, 2), (key1981, 2), (key1997, 2), (key1976, -2), (key1983, -2), (key1983, -2), (key2218, 2), (key2218, 2), (key2262, 2), (key1976, -1), (key1983, -1), (key1976, -1), (key2224, -1), (key1983, -1), (key2224, -1), (key2218, -2), (key2262, -2), (key2262, -2), (key1981, -1), (key1997, -1), (key1981, -1), (key2266, -1), (key1997, -1), (key2266, -1), (key1983, 4), (key1983, 4), (key2224, 4)]

theorem rawRowCheck17277 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form12 = rawRow17277 := by decide +kernel

def row17277 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

theorem rowCheck17277 : row17277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17277 := by decide +kernel

theorem rowEval17277 (x : Key → ℝ) : Integer.Sparse.eval row17277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, -1, 2] GramFunctions.Block4.form12) x := by
  rw [rowCheck17277, Integer.Sparse.eval_collectBalanced, rawRowCheck17277]

def rawRow17278 : Integer.Sparse Key := [(key1981, 2), (key1997, 2), (key1981, 2), (key1983, -2), (key1976, -2), (key1983, -2), (key2218, 2), (key2262, 2), (key2218, 2), (key1983, -1), (key1976, -1), (key2224, -1), (key1976, -1), (key2224, -1), (key1983, -1), (key2262, -2), (key2218, -2), (key2262, -2), (key1997, -1), (key1981, -1), (key2266, -1), (key1981, -1), (key2266, -1), (key1997, -1), (key1983, 4), (key2224, 4), (key1983, 4)]

theorem rawRowCheck17278 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form12 = rawRow17278 := by decide +kernel

def row17278 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

theorem rowCheck17278 : row17278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17278 := by decide +kernel

theorem rowEval17278 (x : Key → ℝ) : Integer.Sparse.eval row17278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -1, 2, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17278, Integer.Sparse.eval_collectBalanced, rawRowCheck17278]

def rawRow17279 : Integer.Sparse Key := [(key1997, 2), (key1981, 2), (key1981, 2), (key1983, -2), (key1983, -2), (key1976, -2), (key2262, 2), (key2218, 2), (key2218, 2), (key2224, -1), (key2224, -1), (key1983, -1), (key1983, -1), (key1976, -1), (key1976, -1), (key2262, -2), (key2262, -2), (key2218, -2), (key2266, -1), (key2266, -1), (key1997, -1), (key1997, -1), (key1981, -1), (key1981, -1), (key2224, 4), (key1983, 4), (key1983, 4)]

theorem rawRowCheck17279 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form12 = rawRow17279 := by decide +kernel

def row17279 : Integer.Sparse Key := [(key1976, -4), (key1981, 2), (key1983, 2), (key2218, 2), (key2224, 2), (key2262, -2), (key2266, -2)]

theorem rowCheck17279 : row17279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow17279 := by decide +kernel

theorem rowEval17279 (x : Key → ℝ) : Integer.Sparse.eval row17279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -1, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck17279, Integer.Sparse.eval_collectBalanced, rawRowCheck17279]

end MUB6.Certificate.GramRows

end OAI
