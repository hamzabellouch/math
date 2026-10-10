import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block5
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block24

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow18304 : Integer.Sparse Key := [(key2818, -1), (key2818, -1), (key2818, -1), (key2818, -1), (key2818, -1), (key2818, -1), (key2813, 2), (key2813, 2), (key2813, 2), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2710, -2), (key2710, -2), (key2710, -2), (key2955, -1), (key2955, -1), (key2955, -1), (key2955, -1), (key2955, -1), (key2955, -1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key3103, 2), (key3103, 2), (key3103, 2), (key3066, -2), (key3066, -2), (key3066, -2)]

theorem rawRowCheck18304 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form15 = rawRow18304 := by decide +kernel

def row18304 : Integer.Sparse Key := [(key2710, -6), (key2715, 6), (key2742, 6), (key2813, 6), (key2818, -6), (key2955, -6), (key3066, -6), (key3103, 6)]

theorem rowCheck18304 : row18304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18304 := by decide +kernel

theorem rowEval18304 (x : Key → ℝ) : Integer.Sparse.eval row18304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck18304, Integer.Sparse.eval_collectBalanced, rawRowCheck18304]

def rawRow18305 : Integer.Sparse Key := [(key2953, -1), (key2955, -1), (key2953, -1), (key2979, -1), (key2955, -1), (key2979, -1), (key2955, 2), (key2955, 2), (key2979, 2), (key2740, 1), (key2742, 1), (key2740, 1), (key2900, 1), (key2742, 1), (key2900, 1), (key2742, -2), (key2742, -2), (key2900, -2), (key2682, -1), (key2689, -1), (key2682, -1), (key2715, -1), (key2689, -1), (key2715, -1), (key2682, 1), (key2689, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2818, 1), (key2679, 2), (key2679, 2), (key2710, 2), (key2679, -2), (key3047, -2), (key3096, -2)]

theorem rawRowCheck18305 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form15 = rawRow18305 := by decide +kernel

def row18305 : Integer.Sparse Key := [(key2679, 2), (key2710, 2), (key2715, -2), (key2740, 2), (key2742, -2), (key2818, 2), (key2953, -2), (key2955, 2), (key3047, -2), (key3096, -2)]

theorem rowCheck18305 : row18305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18305 := by decide +kernel

theorem rowEval18305 (x : Key → ℝ) : Integer.Sparse.eval row18305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form15) x := by
  rw [rowCheck18305, Integer.Sparse.eval_collectBalanced, rawRowCheck18305]

def rawRow18306 : Integer.Sparse Key := [(key2955, -1), (key2953, -1), (key2979, -1), (key2953, -1), (key2979, -1), (key2955, -1), (key2955, 2), (key2979, 2), (key2955, 2), (key2742, 1), (key2740, 1), (key2900, 1), (key2740, 1), (key2900, 1), (key2742, 1), (key2742, -2), (key2900, -2), (key2742, -2), (key2689, -1), (key2682, -1), (key2715, -1), (key2682, -1), (key2715, -1), (key2689, -1), (key2689, 1), (key2682, 1), (key2818, 1), (key2682, 1), (key2818, 1), (key2689, 1), (key2679, 2), (key2710, 2), (key2679, 2), (key2679, -2), (key3096, -2), (key3047, -2)]

theorem rawRowCheck18306 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form15 = rawRow18306 := by decide +kernel

def row18306 : Integer.Sparse Key := [(key2679, 2), (key2710, 2), (key2715, -2), (key2740, 2), (key2742, -2), (key2818, 2), (key2953, -2), (key2955, 2), (key3047, -2), (key3096, -2)]

theorem rowCheck18306 : row18306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18306 := by decide +kernel

theorem rowEval18306 (x : Key → ℝ) : Integer.Sparse.eval row18306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck18306, Integer.Sparse.eval_collectBalanced, rawRowCheck18306]

def rawRow18307 : Integer.Sparse Key := [(key2979, -1), (key2979, -1), (key2955, -1), (key2955, -1), (key2953, -1), (key2953, -1), (key2979, 2), (key2955, 2), (key2955, 2), (key2900, 1), (key2900, 1), (key2742, 1), (key2742, 1), (key2740, 1), (key2740, 1), (key2900, -2), (key2742, -2), (key2742, -2), (key2715, -1), (key2715, -1), (key2689, -1), (key2689, -1), (key2682, -1), (key2682, -1), (key2818, 1), (key2818, 1), (key2689, 1), (key2689, 1), (key2682, 1), (key2682, 1), (key2710, 2), (key2679, 2), (key2679, 2), (key2813, -2), (key2679, -2), (key3047, -2)]

theorem rawRowCheck18307 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form15 = rawRow18307 := by decide +kernel

def row18307 : Integer.Sparse Key := [(key2679, 2), (key2710, 2), (key2715, -2), (key2740, 2), (key2742, -2), (key2813, -2), (key2818, 2), (key2953, -2), (key2955, 2), (key3047, -2)]

theorem rowCheck18307 : row18307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18307 := by decide +kernel

theorem rowEval18307 (x : Key → ℝ) : Integer.Sparse.eval row18307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck18307, Integer.Sparse.eval_collectBalanced, rawRowCheck18307]

def rawRow18308 : Integer.Sparse Key := [(key2955, -1), (key2955, -1), (key2955, -1), (key2955, -1), (key2955, -1), (key2955, -1), (key2953, 2), (key2953, 2), (key2953, 2), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2742, 1), (key2740, -2), (key2740, -2), (key2740, -2), (key2818, -1), (key2818, -1), (key2818, -1), (key2818, -1), (key2818, -1), (key2818, -1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2715, 1), (key2813, 2), (key2813, 2), (key2813, 2), (key2710, -2), (key2710, -2), (key2710, -2)]

theorem rawRowCheck18308 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form15 = rawRow18308 := by decide +kernel

def row18308 : Integer.Sparse Key := [(key2710, -6), (key2715, 6), (key2740, -6), (key2742, 6), (key2813, 6), (key2818, -6), (key2953, 6), (key2955, -6)]

theorem rowCheck18308 : row18308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18308 := by decide +kernel

theorem rowEval18308 (x : Key → ℝ) : Integer.Sparse.eval row18308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form15) x := by
  rw [rowCheck18308, Integer.Sparse.eval_collectBalanced, rawRowCheck18308]

def rawRow18309 : Integer.Sparse Key := [(key2686, 2), (key2822, 2), (key2957, 2), (key2693, -1), (key2694, -1), (key2822, -1), (key2957, -1), (key2834, -1), (key2963, -1), (key2686, 2), (key2822, 2), (key2957, 2), (key2719, -1), (key2744, -1), (key2822, -1), (key2957, -1), (key2907, -1), (key2986, -1), (key2693, -1), (key2694, -1), (key2822, -1), (key2957, -1), (key2834, -1), (key2963, -1), (key2719, -1), (key2744, -1), (key2822, -1), (key2957, -1), (key2907, -1), (key2986, -1), (key2731, 2), (key2750, 2), (key2834, 2), (key2963, 2), (key2907, 2), (key2986, 2)]

theorem rawRowCheck18309 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form16 = rawRow18309 := by decide +kernel

def row18309 : Integer.Sparse Key := [(key2686, 4), (key2693, -2), (key2694, -2), (key2719, -2), (key2731, 2), (key2744, -2), (key2750, 2)]

theorem rowCheck18309 : row18309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18309 := by decide +kernel

theorem rowEval18309 (x : Key → ℝ) : Integer.Sparse.eval row18309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck18309, Integer.Sparse.eval_collectBalanced, rawRowCheck18309]

def rawRow18310 : Integer.Sparse Key := [(key2686, 2), (key2957, 2), (key2822, 2), (key2694, -1), (key2693, -1), (key2957, -1), (key2822, -1), (key2963, -1), (key2834, -1), (key2686, 2), (key2957, 2), (key2822, 2), (key2744, -1), (key2719, -1), (key2957, -1), (key2822, -1), (key2986, -1), (key2907, -1), (key2694, -1), (key2693, -1), (key2957, -1), (key2822, -1), (key2963, -1), (key2834, -1), (key2744, -1), (key2719, -1), (key2957, -1), (key2822, -1), (key2986, -1), (key2907, -1), (key2750, 2), (key2731, 2), (key2963, 2), (key2834, 2), (key2986, 2), (key2907, 2)]

theorem rawRowCheck18310 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form16 = rawRow18310 := by decide +kernel

def row18310 : Integer.Sparse Key := [(key2686, 4), (key2693, -2), (key2694, -2), (key2719, -2), (key2731, 2), (key2744, -2), (key2750, 2)]

theorem rowCheck18310 : row18310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18310 := by decide +kernel

theorem rowEval18310 (x : Key → ℝ) : Integer.Sparse.eval row18310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck18310, Integer.Sparse.eval_collectBalanced, rawRowCheck18310]

def rawRow18311 : Integer.Sparse Key := [(key2822, 2), (key2686, 2), (key2957, 2), (key2822, -1), (key2834, -1), (key2693, -1), (key2963, -1), (key2694, -1), (key2957, -1), (key2822, 2), (key2686, 2), (key2957, 2), (key2822, -1), (key2907, -1), (key2719, -1), (key2986, -1), (key2744, -1), (key2957, -1), (key2822, -1), (key2834, -1), (key2693, -1), (key2963, -1), (key2694, -1), (key2957, -1), (key2822, -1), (key2907, -1), (key2719, -1), (key2986, -1), (key2744, -1), (key2957, -1), (key2834, 2), (key2907, 2), (key2731, 2), (key2986, 2), (key2750, 2), (key2963, 2)]

theorem rawRowCheck18311 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form16 = rawRow18311 := by decide +kernel

def row18311 : Integer.Sparse Key := [(key2686, 4), (key2693, -2), (key2694, -2), (key2719, -2), (key2731, 2), (key2744, -2), (key2750, 2)]

theorem rowCheck18311 : row18311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18311 := by decide +kernel

theorem rowEval18311 (x : Key → ℝ) : Integer.Sparse.eval row18311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck18311, Integer.Sparse.eval_collectBalanced, rawRowCheck18311]

def rawRow18312 : Integer.Sparse Key := [(key2822, 2), (key2957, 2), (key2686, 2), (key2834, -1), (key2822, -1), (key2963, -1), (key2693, -1), (key2957, -1), (key2694, -1), (key2822, 2), (key2957, 2), (key2686, 2), (key2907, -1), (key2822, -1), (key2986, -1), (key2719, -1), (key2957, -1), (key2744, -1), (key2834, -1), (key2822, -1), (key2963, -1), (key2693, -1), (key2957, -1), (key2694, -1), (key2907, -1), (key2822, -1), (key2986, -1), (key2719, -1), (key2957, -1), (key2744, -1), (key2907, 2), (key2834, 2), (key2986, 2), (key2731, 2), (key2963, 2), (key2750, 2)]

theorem rawRowCheck18312 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form16 = rawRow18312 := by decide +kernel

def row18312 : Integer.Sparse Key := [(key2686, 4), (key2693, -2), (key2694, -2), (key2719, -2), (key2731, 2), (key2744, -2), (key2750, 2)]

theorem rowCheck18312 : row18312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18312 := by decide +kernel

theorem rowEval18312 (x : Key → ℝ) : Integer.Sparse.eval row18312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck18312, Integer.Sparse.eval_collectBalanced, rawRowCheck18312]

def rawRow18313 : Integer.Sparse Key := [(key2957, 2), (key2686, 2), (key2822, 2), (key2957, -1), (key2963, -1), (key2694, -1), (key2834, -1), (key2693, -1), (key2822, -1), (key2957, 2), (key2686, 2), (key2822, 2), (key2957, -1), (key2986, -1), (key2744, -1), (key2907, -1), (key2719, -1), (key2822, -1), (key2957, -1), (key2963, -1), (key2694, -1), (key2834, -1), (key2693, -1), (key2822, -1), (key2957, -1), (key2986, -1), (key2744, -1), (key2907, -1), (key2719, -1), (key2822, -1), (key2963, 2), (key2986, 2), (key2750, 2), (key2907, 2), (key2731, 2), (key2834, 2)]

theorem rawRowCheck18313 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form16 = rawRow18313 := by decide +kernel

def row18313 : Integer.Sparse Key := [(key2686, 4), (key2693, -2), (key2694, -2), (key2719, -2), (key2731, 2), (key2744, -2), (key2750, 2)]

theorem rowCheck18313 : row18313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18313 := by decide +kernel

theorem rowEval18313 (x : Key → ℝ) : Integer.Sparse.eval row18313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck18313, Integer.Sparse.eval_collectBalanced, rawRowCheck18313]

def rawRow18314 : Integer.Sparse Key := [(key2957, 2), (key2822, 2), (key2686, 2), (key2963, -1), (key2957, -1), (key2834, -1), (key2694, -1), (key2822, -1), (key2693, -1), (key2957, 2), (key2822, 2), (key2686, 2), (key2986, -1), (key2957, -1), (key2907, -1), (key2744, -1), (key2822, -1), (key2719, -1), (key2963, -1), (key2957, -1), (key2834, -1), (key2694, -1), (key2822, -1), (key2693, -1), (key2986, -1), (key2957, -1), (key2907, -1), (key2744, -1), (key2822, -1), (key2719, -1), (key2986, 2), (key2963, 2), (key2907, 2), (key2750, 2), (key2834, 2), (key2731, 2)]

theorem rawRowCheck18314 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form16 = rawRow18314 := by decide +kernel

def row18314 : Integer.Sparse Key := [(key2686, 4), (key2693, -2), (key2694, -2), (key2719, -2), (key2731, 2), (key2744, -2), (key2750, 2)]

theorem rowCheck18314 : row18314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18314 := by decide +kernel

theorem rowEval18314 (x : Key → ℝ) : Integer.Sparse.eval row18314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck18314, Integer.Sparse.eval_collectBalanced, rawRowCheck18314]

def rawRow18315 : Integer.Sparse Key := [(key2693, 2), (key2693, 2), (key2963, 2), (key2686, -1), (key2694, -1), (key2686, -1), (key2957, -1), (key2694, -1), (key2957, -1), (key2719, 2), (key2719, 2), (key2986, 2), (key2686, -1), (key2744, -1), (key2686, -1), (key2957, -1), (key2744, -1), (key2957, -1), (key2719, -1), (key2731, -1), (key2719, -1), (key2986, -1), (key2731, -1), (key2986, -1), (key2693, -1), (key2750, -1), (key2693, -1), (key2963, -1), (key2750, -1), (key2963, -1), (key2694, 2), (key2744, 2), (key2694, 2), (key2957, 2), (key2744, 2), (key2957, 2)]

theorem rawRowCheck18315 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form16 = rawRow18315 := by decide +kernel

def row18315 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

theorem rowCheck18315 : row18315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18315 := by decide +kernel

theorem rowEval18315 (x : Key → ℝ) : Integer.Sparse.eval row18315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck18315, Integer.Sparse.eval_collectBalanced, rawRowCheck18315]

def rawRow18316 : Integer.Sparse Key := [(key2693, 2), (key2963, 2), (key2693, 2), (key2694, -1), (key2686, -1), (key2957, -1), (key2686, -1), (key2957, -1), (key2694, -1), (key2719, 2), (key2986, 2), (key2719, 2), (key2744, -1), (key2686, -1), (key2957, -1), (key2686, -1), (key2957, -1), (key2744, -1), (key2731, -1), (key2719, -1), (key2986, -1), (key2719, -1), (key2986, -1), (key2731, -1), (key2750, -1), (key2693, -1), (key2963, -1), (key2693, -1), (key2963, -1), (key2750, -1), (key2744, 2), (key2694, 2), (key2957, 2), (key2694, 2), (key2957, 2), (key2744, 2)]

theorem rawRowCheck18316 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form16 = rawRow18316 := by decide +kernel

def row18316 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

theorem rowCheck18316 : row18316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18316 := by decide +kernel

theorem rowEval18316 (x : Key → ℝ) : Integer.Sparse.eval row18316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck18316, Integer.Sparse.eval_collectBalanced, rawRowCheck18316]

def rawRow18317 : Integer.Sparse Key := [(key2963, 2), (key2693, 2), (key2693, 2), (key2957, -1), (key2957, -1), (key2694, -1), (key2694, -1), (key2686, -1), (key2686, -1), (key2986, 2), (key2719, 2), (key2719, 2), (key2957, -1), (key2957, -1), (key2744, -1), (key2744, -1), (key2686, -1), (key2686, -1), (key2986, -1), (key2986, -1), (key2731, -1), (key2731, -1), (key2719, -1), (key2719, -1), (key2963, -1), (key2963, -1), (key2750, -1), (key2750, -1), (key2693, -1), (key2693, -1), (key2957, 2), (key2957, 2), (key2744, 2), (key2744, 2), (key2694, 2), (key2694, 2)]

theorem rawRowCheck18317 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form16 = rawRow18317 := by decide +kernel

def row18317 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

theorem rowCheck18317 : row18317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18317 := by decide +kernel

theorem rowEval18317 (x : Key → ℝ) : Integer.Sparse.eval row18317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck18317, Integer.Sparse.eval_collectBalanced, rawRowCheck18317]

def rawRow18318 : Integer.Sparse Key := [(key2694, 2), (key2694, 2), (key2834, 2), (key2686, -1), (key2693, -1), (key2686, -1), (key2822, -1), (key2693, -1), (key2822, -1), (key2744, 2), (key2744, 2), (key2907, 2), (key2686, -1), (key2719, -1), (key2686, -1), (key2822, -1), (key2719, -1), (key2822, -1), (key2744, -1), (key2750, -1), (key2744, -1), (key2907, -1), (key2750, -1), (key2907, -1), (key2694, -1), (key2731, -1), (key2694, -1), (key2834, -1), (key2731, -1), (key2834, -1), (key2693, 2), (key2719, 2), (key2693, 2), (key2822, 2), (key2719, 2), (key2822, 2)]

theorem rawRowCheck18318 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form16 = rawRow18318 := by decide +kernel

def row18318 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

theorem rowCheck18318 : row18318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18318 := by decide +kernel

theorem rowEval18318 (x : Key → ℝ) : Integer.Sparse.eval row18318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck18318, Integer.Sparse.eval_collectBalanced, rawRowCheck18318]

def rawRow18319 : Integer.Sparse Key := [(key2694, 2), (key2834, 2), (key2694, 2), (key2693, -1), (key2686, -1), (key2822, -1), (key2686, -1), (key2822, -1), (key2693, -1), (key2744, 2), (key2907, 2), (key2744, 2), (key2719, -1), (key2686, -1), (key2822, -1), (key2686, -1), (key2822, -1), (key2719, -1), (key2750, -1), (key2744, -1), (key2907, -1), (key2744, -1), (key2907, -1), (key2750, -1), (key2731, -1), (key2694, -1), (key2834, -1), (key2694, -1), (key2834, -1), (key2731, -1), (key2719, 2), (key2693, 2), (key2822, 2), (key2693, 2), (key2822, 2), (key2719, 2)]

theorem rawRowCheck18319 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form16 = rawRow18319 := by decide +kernel

def row18319 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

theorem rowCheck18319 : row18319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18319 := by decide +kernel

theorem rowEval18319 (x : Key → ℝ) : Integer.Sparse.eval row18319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck18319, Integer.Sparse.eval_collectBalanced, rawRowCheck18319]

def rawRow18320 : Integer.Sparse Key := [(key2834, 2), (key2694, 2), (key2694, 2), (key2822, -1), (key2822, -1), (key2693, -1), (key2693, -1), (key2686, -1), (key2686, -1), (key2907, 2), (key2744, 2), (key2744, 2), (key2822, -1), (key2822, -1), (key2719, -1), (key2719, -1), (key2686, -1), (key2686, -1), (key2907, -1), (key2907, -1), (key2750, -1), (key2750, -1), (key2744, -1), (key2744, -1), (key2834, -1), (key2834, -1), (key2731, -1), (key2731, -1), (key2694, -1), (key2694, -1), (key2822, 2), (key2822, 2), (key2719, 2), (key2719, 2), (key2693, 2), (key2693, 2)]

theorem rawRowCheck18320 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form16 = rawRow18320 := by decide +kernel

def row18320 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

theorem rowCheck18320 : row18320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18320 := by decide +kernel

theorem rowEval18320 (x : Key → ℝ) : Integer.Sparse.eval row18320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck18320, Integer.Sparse.eval_collectBalanced, rawRowCheck18320]

def rawRow18321 : Integer.Sparse Key := [(key2719, 2), (key2719, 2), (key2986, 2), (key2719, -1), (key2731, -1), (key2719, -1), (key2986, -1), (key2731, -1), (key2986, -1), (key2693, 2), (key2693, 2), (key2963, 2), (key2693, -1), (key2750, -1), (key2693, -1), (key2963, -1), (key2750, -1), (key2963, -1), (key2686, -1), (key2694, -1), (key2686, -1), (key2957, -1), (key2694, -1), (key2957, -1), (key2686, -1), (key2744, -1), (key2686, -1), (key2957, -1), (key2744, -1), (key2957, -1), (key2694, 2), (key2744, 2), (key2694, 2), (key2957, 2), (key2744, 2), (key2957, 2)]

theorem rawRowCheck18321 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form16 = rawRow18321 := by decide +kernel

def row18321 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

theorem rowCheck18321 : row18321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18321 := by decide +kernel

theorem rowEval18321 (x : Key → ℝ) : Integer.Sparse.eval row18321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form16) x := by
  rw [rowCheck18321, Integer.Sparse.eval_collectBalanced, rawRowCheck18321]

def rawRow18322 : Integer.Sparse Key := [(key2719, 2), (key2986, 2), (key2719, 2), (key2731, -1), (key2719, -1), (key2986, -1), (key2719, -1), (key2986, -1), (key2731, -1), (key2693, 2), (key2963, 2), (key2693, 2), (key2750, -1), (key2693, -1), (key2963, -1), (key2693, -1), (key2963, -1), (key2750, -1), (key2694, -1), (key2686, -1), (key2957, -1), (key2686, -1), (key2957, -1), (key2694, -1), (key2744, -1), (key2686, -1), (key2957, -1), (key2686, -1), (key2957, -1), (key2744, -1), (key2744, 2), (key2694, 2), (key2957, 2), (key2694, 2), (key2957, 2), (key2744, 2)]

theorem rawRowCheck18322 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form16 = rawRow18322 := by decide +kernel

def row18322 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

theorem rowCheck18322 : row18322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18322 := by decide +kernel

theorem rowEval18322 (x : Key → ℝ) : Integer.Sparse.eval row18322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck18322, Integer.Sparse.eval_collectBalanced, rawRowCheck18322]

def rawRow18323 : Integer.Sparse Key := [(key2986, 2), (key2719, 2), (key2719, 2), (key2986, -1), (key2986, -1), (key2731, -1), (key2731, -1), (key2719, -1), (key2719, -1), (key2963, 2), (key2693, 2), (key2693, 2), (key2963, -1), (key2963, -1), (key2750, -1), (key2750, -1), (key2693, -1), (key2693, -1), (key2957, -1), (key2957, -1), (key2694, -1), (key2694, -1), (key2686, -1), (key2686, -1), (key2957, -1), (key2957, -1), (key2744, -1), (key2744, -1), (key2686, -1), (key2686, -1), (key2957, 2), (key2957, 2), (key2744, 2), (key2744, 2), (key2694, 2), (key2694, 2)]

theorem rawRowCheck18323 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form16 = rawRow18323 := by decide +kernel

def row18323 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

theorem rowCheck18323 : row18323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18323 := by decide +kernel

theorem rowEval18323 (x : Key → ℝ) : Integer.Sparse.eval row18323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck18323, Integer.Sparse.eval_collectBalanced, rawRowCheck18323]

def rawRow18324 : Integer.Sparse Key := [(key2731, 2), (key2731, 2), (key2731, 2), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2750, 2), (key2750, 2), (key2750, 2), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2686, 2), (key2686, 2), (key2686, 2), (key2686, 2), (key2686, 2), (key2686, 2)]

theorem rawRowCheck18324 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form16 = rawRow18324 := by decide +kernel

def row18324 : Integer.Sparse Key := [(key2686, 12), (key2693, -6), (key2694, -6), (key2719, -6), (key2731, 6), (key2744, -6), (key2750, 6)]

theorem rowCheck18324 : row18324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18324 := by decide +kernel

theorem rowEval18324 (x : Key → ℝ) : Integer.Sparse.eval row18324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck18324, Integer.Sparse.eval_collectBalanced, rawRowCheck18324]

def rawRow18325 : Integer.Sparse Key := [(key2744, 2), (key2744, 2), (key2907, 2), (key2744, -1), (key2750, -1), (key2744, -1), (key2907, -1), (key2750, -1), (key2907, -1), (key2694, 2), (key2694, 2), (key2834, 2), (key2694, -1), (key2731, -1), (key2694, -1), (key2834, -1), (key2731, -1), (key2834, -1), (key2686, -1), (key2693, -1), (key2686, -1), (key2822, -1), (key2693, -1), (key2822, -1), (key2686, -1), (key2719, -1), (key2686, -1), (key2822, -1), (key2719, -1), (key2822, -1), (key2693, 2), (key2719, 2), (key2693, 2), (key2822, 2), (key2719, 2), (key2822, 2)]

theorem rawRowCheck18325 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form16 = rawRow18325 := by decide +kernel

def row18325 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

theorem rowCheck18325 : row18325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18325 := by decide +kernel

theorem rowEval18325 (x : Key → ℝ) : Integer.Sparse.eval row18325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form16) x := by
  rw [rowCheck18325, Integer.Sparse.eval_collectBalanced, rawRowCheck18325]

def rawRow18326 : Integer.Sparse Key := [(key2744, 2), (key2907, 2), (key2744, 2), (key2750, -1), (key2744, -1), (key2907, -1), (key2744, -1), (key2907, -1), (key2750, -1), (key2694, 2), (key2834, 2), (key2694, 2), (key2731, -1), (key2694, -1), (key2834, -1), (key2694, -1), (key2834, -1), (key2731, -1), (key2693, -1), (key2686, -1), (key2822, -1), (key2686, -1), (key2822, -1), (key2693, -1), (key2719, -1), (key2686, -1), (key2822, -1), (key2686, -1), (key2822, -1), (key2719, -1), (key2719, 2), (key2693, 2), (key2822, 2), (key2693, 2), (key2822, 2), (key2719, 2)]

theorem rawRowCheck18326 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form16 = rawRow18326 := by decide +kernel

def row18326 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

theorem rowCheck18326 : row18326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18326 := by decide +kernel

theorem rowEval18326 (x : Key → ℝ) : Integer.Sparse.eval row18326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck18326, Integer.Sparse.eval_collectBalanced, rawRowCheck18326]

def rawRow18327 : Integer.Sparse Key := [(key2907, 2), (key2744, 2), (key2744, 2), (key2907, -1), (key2907, -1), (key2750, -1), (key2750, -1), (key2744, -1), (key2744, -1), (key2834, 2), (key2694, 2), (key2694, 2), (key2834, -1), (key2834, -1), (key2731, -1), (key2731, -1), (key2694, -1), (key2694, -1), (key2822, -1), (key2822, -1), (key2693, -1), (key2693, -1), (key2686, -1), (key2686, -1), (key2822, -1), (key2822, -1), (key2719, -1), (key2719, -1), (key2686, -1), (key2686, -1), (key2822, 2), (key2822, 2), (key2719, 2), (key2719, 2), (key2693, 2), (key2693, 2)]

theorem rawRowCheck18327 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form16 = rawRow18327 := by decide +kernel

def row18327 : Integer.Sparse Key := [(key2686, -4), (key2693, 2), (key2694, 2), (key2719, 2), (key2731, -2), (key2744, 2), (key2750, -2)]

theorem rowCheck18327 : row18327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18327 := by decide +kernel

theorem rowEval18327 (x : Key → ℝ) : Integer.Sparse.eval row18327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck18327, Integer.Sparse.eval_collectBalanced, rawRowCheck18327]

def rawRow18328 : Integer.Sparse Key := [(key2750, 2), (key2750, 2), (key2750, 2), (key2744, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2744, -1), (key2731, 2), (key2731, 2), (key2731, 2), (key2694, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2694, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2719, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2693, -1), (key2686, 2), (key2686, 2), (key2686, 2), (key2686, 2), (key2686, 2), (key2686, 2)]

theorem rawRowCheck18328 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form16 = rawRow18328 := by decide +kernel

def row18328 : Integer.Sparse Key := [(key2686, 12), (key2693, -6), (key2694, -6), (key2719, -6), (key2731, 6), (key2744, -6), (key2750, 6)]

theorem rowCheck18328 : row18328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18328 := by decide +kernel

theorem rowEval18328 (x : Key → ℝ) : Integer.Sparse.eval row18328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form16) x := by
  rw [rowCheck18328, Integer.Sparse.eval_collectBalanced, rawRowCheck18328]

def rawRow18329 : Integer.Sparse Key := [(key2114, 4), (key2118, 4), (key2122, 4), (key2114, -2), (key2118, -2), (key2156, -2), (key2183, -2), (key2162, -2), (key2185, -2), (key2114, -2), (key2118, -2), (key2156, -2), (key2183, -2), (key2162, -2), (key2185, -2), (key2156, 4), (key2183, 4), (key2285, 4)]

theorem rawRowCheck18329 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form17 = rawRow18329 := by decide +kernel

def row18329 : Integer.Sparse Key := [(key2122, 4), (key2162, -4), (key2185, -4), (key2285, 4)]

theorem rowCheck18329 : row18329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18329 := by decide +kernel

theorem rowEval18329 (x : Key → ℝ) : Integer.Sparse.eval row18329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18329, Integer.Sparse.eval_collectBalanced, rawRowCheck18329]

def rawRow18330 : Integer.Sparse Key := [(key2118, 4), (key2114, 4), (key2122, 4), (key2118, -2), (key2114, -2), (key2183, -2), (key2156, -2), (key2185, -2), (key2162, -2), (key2118, -2), (key2114, -2), (key2183, -2), (key2156, -2), (key2185, -2), (key2162, -2), (key2183, 4), (key2156, 4), (key2285, 4)]

theorem rawRowCheck18330 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form17 = rawRow18330 := by decide +kernel

def row18330 : Integer.Sparse Key := [(key2122, 4), (key2162, -4), (key2185, -4), (key2285, 4)]

theorem rowCheck18330 : row18330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18330 := by decide +kernel

theorem rowEval18330 (x : Key → ℝ) : Integer.Sparse.eval row18330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck18330, Integer.Sparse.eval_collectBalanced, rawRowCheck18330]

def rawRow18331 : Integer.Sparse Key := [(key2114, 4), (key2122, 4), (key2118, 4), (key2156, -2), (key2162, -2), (key2114, -2), (key2185, -2), (key2118, -2), (key2183, -2), (key2156, -2), (key2162, -2), (key2114, -2), (key2185, -2), (key2118, -2), (key2183, -2), (key2156, 4), (key2285, 4), (key2183, 4)]

theorem rawRowCheck18331 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form17 = rawRow18331 := by decide +kernel

def row18331 : Integer.Sparse Key := [(key2122, 4), (key2162, -4), (key2185, -4), (key2285, 4)]

theorem rowCheck18331 : row18331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18331 := by decide +kernel

theorem rowEval18331 (x : Key → ℝ) : Integer.Sparse.eval row18331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18331, Integer.Sparse.eval_collectBalanced, rawRowCheck18331]

def rawRow18332 : Integer.Sparse Key := [(key2122, 4), (key2114, 4), (key2118, 4), (key2162, -2), (key2156, -2), (key2185, -2), (key2114, -2), (key2183, -2), (key2118, -2), (key2162, -2), (key2156, -2), (key2185, -2), (key2114, -2), (key2183, -2), (key2118, -2), (key2285, 4), (key2156, 4), (key2183, 4)]

theorem rawRowCheck18332 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form17 = rawRow18332 := by decide +kernel

def row18332 : Integer.Sparse Key := [(key2122, 4), (key2162, -4), (key2185, -4), (key2285, 4)]

theorem rowCheck18332 : row18332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18332 := by decide +kernel

theorem rowEval18332 (x : Key → ℝ) : Integer.Sparse.eval row18332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18332, Integer.Sparse.eval_collectBalanced, rawRowCheck18332]

def rawRow18333 : Integer.Sparse Key := [(key2118, 4), (key2122, 4), (key2114, 4), (key2183, -2), (key2185, -2), (key2118, -2), (key2162, -2), (key2114, -2), (key2156, -2), (key2183, -2), (key2185, -2), (key2118, -2), (key2162, -2), (key2114, -2), (key2156, -2), (key2183, 4), (key2285, 4), (key2156, 4)]

theorem rawRowCheck18333 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form17 = rawRow18333 := by decide +kernel

def row18333 : Integer.Sparse Key := [(key2122, 4), (key2162, -4), (key2185, -4), (key2285, 4)]

theorem rowCheck18333 : row18333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18333 := by decide +kernel

theorem rowEval18333 (x : Key → ℝ) : Integer.Sparse.eval row18333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck18333, Integer.Sparse.eval_collectBalanced, rawRowCheck18333]

def rawRow18334 : Integer.Sparse Key := [(key2122, 4), (key2118, 4), (key2114, 4), (key2185, -2), (key2183, -2), (key2162, -2), (key2118, -2), (key2156, -2), (key2114, -2), (key2185, -2), (key2183, -2), (key2162, -2), (key2118, -2), (key2156, -2), (key2114, -2), (key2285, 4), (key2183, 4), (key2156, 4)]

theorem rawRowCheck18334 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form17 = rawRow18334 := by decide +kernel

def row18334 : Integer.Sparse Key := [(key2122, 4), (key2162, -4), (key2185, -4), (key2285, 4)]

theorem rowCheck18334 : row18334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18334 := by decide +kernel

theorem rowEval18334 (x : Key → ℝ) : Integer.Sparse.eval row18334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18334, Integer.Sparse.eval_collectBalanced, rawRowCheck18334]

def rawRow18335 : Integer.Sparse Key := [(key2156, 4), (key2162, 4), (key2162, 4), (key2114, -2), (key2122, -2), (key2114, -2), (key2185, -2), (key2122, -2), (key2185, -2), (key2156, -2), (key2162, -2), (key2156, -2), (key2285, -2), (key2162, -2), (key2285, -2), (key2114, 4), (key2185, 4), (key2185, 4)]

theorem rawRowCheck18335 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form17 = rawRow18335 := by decide +kernel

def row18335 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

theorem rowCheck18335 : row18335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18335 := by decide +kernel

theorem rowEval18335 (x : Key → ℝ) : Integer.Sparse.eval row18335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18335, Integer.Sparse.eval_collectBalanced, rawRowCheck18335]

def rawRow18336 : Integer.Sparse Key := [(key2162, 4), (key2156, 4), (key2162, 4), (key2122, -2), (key2114, -2), (key2185, -2), (key2114, -2), (key2185, -2), (key2122, -2), (key2162, -2), (key2156, -2), (key2285, -2), (key2156, -2), (key2285, -2), (key2162, -2), (key2185, 4), (key2114, 4), (key2185, 4)]

theorem rawRowCheck18336 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form17 = rawRow18336 := by decide +kernel

def row18336 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

theorem rowCheck18336 : row18336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18336 := by decide +kernel

theorem rowEval18336 (x : Key → ℝ) : Integer.Sparse.eval row18336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18336, Integer.Sparse.eval_collectBalanced, rawRowCheck18336]

def rawRow18337 : Integer.Sparse Key := [(key2162, 4), (key2162, 4), (key2156, 4), (key2185, -2), (key2185, -2), (key2122, -2), (key2122, -2), (key2114, -2), (key2114, -2), (key2285, -2), (key2285, -2), (key2162, -2), (key2162, -2), (key2156, -2), (key2156, -2), (key2185, 4), (key2185, 4), (key2114, 4)]

theorem rawRowCheck18337 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form17 = rawRow18337 := by decide +kernel

def row18337 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

theorem rowCheck18337 : row18337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18337 := by decide +kernel

theorem rowEval18337 (x : Key → ℝ) : Integer.Sparse.eval row18337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18337, Integer.Sparse.eval_collectBalanced, rawRowCheck18337]

def rawRow18338 : Integer.Sparse Key := [(key2183, 4), (key2185, 4), (key2185, 4), (key2118, -2), (key2122, -2), (key2118, -2), (key2162, -2), (key2122, -2), (key2162, -2), (key2183, -2), (key2185, -2), (key2183, -2), (key2285, -2), (key2185, -2), (key2285, -2), (key2118, 4), (key2162, 4), (key2162, 4)]

theorem rawRowCheck18338 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form17 = rawRow18338 := by decide +kernel

def row18338 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

theorem rowCheck18338 : row18338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18338 := by decide +kernel

theorem rowEval18338 (x : Key → ℝ) : Integer.Sparse.eval row18338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck18338, Integer.Sparse.eval_collectBalanced, rawRowCheck18338]

def rawRow18339 : Integer.Sparse Key := [(key2185, 4), (key2183, 4), (key2185, 4), (key2122, -2), (key2118, -2), (key2162, -2), (key2118, -2), (key2162, -2), (key2122, -2), (key2185, -2), (key2183, -2), (key2285, -2), (key2183, -2), (key2285, -2), (key2185, -2), (key2162, 4), (key2118, 4), (key2162, 4)]

theorem rawRowCheck18339 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form17 = rawRow18339 := by decide +kernel

def row18339 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

theorem rowCheck18339 : row18339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18339 := by decide +kernel

theorem rowEval18339 (x : Key → ℝ) : Integer.Sparse.eval row18339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18339, Integer.Sparse.eval_collectBalanced, rawRowCheck18339]

def rawRow18340 : Integer.Sparse Key := [(key2185, 4), (key2185, 4), (key2183, 4), (key2162, -2), (key2162, -2), (key2122, -2), (key2122, -2), (key2118, -2), (key2118, -2), (key2285, -2), (key2285, -2), (key2185, -2), (key2185, -2), (key2183, -2), (key2183, -2), (key2162, 4), (key2162, 4), (key2118, 4)]

theorem rawRowCheck18340 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form17 = rawRow18340 := by decide +kernel

def row18340 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

theorem rowCheck18340 : row18340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18340 := by decide +kernel

theorem rowEval18340 (x : Key → ℝ) : Integer.Sparse.eval row18340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18340, Integer.Sparse.eval_collectBalanced, rawRowCheck18340]

def rawRow18341 : Integer.Sparse Key := [(key2156, 4), (key2162, 4), (key2162, 4), (key2156, -2), (key2162, -2), (key2156, -2), (key2285, -2), (key2162, -2), (key2285, -2), (key2114, -2), (key2122, -2), (key2114, -2), (key2185, -2), (key2122, -2), (key2185, -2), (key2114, 4), (key2185, 4), (key2185, 4)]

theorem rawRowCheck18341 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form17 = rawRow18341 := by decide +kernel

def row18341 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

theorem rowCheck18341 : row18341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18341 := by decide +kernel

theorem rowEval18341 (x : Key → ℝ) : Integer.Sparse.eval row18341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18341, Integer.Sparse.eval_collectBalanced, rawRowCheck18341]

def rawRow18342 : Integer.Sparse Key := [(key2162, 4), (key2156, 4), (key2162, 4), (key2162, -2), (key2156, -2), (key2285, -2), (key2156, -2), (key2285, -2), (key2162, -2), (key2122, -2), (key2114, -2), (key2185, -2), (key2114, -2), (key2185, -2), (key2122, -2), (key2185, 4), (key2114, 4), (key2185, 4)]

theorem rawRowCheck18342 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form17 = rawRow18342 := by decide +kernel

def row18342 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

theorem rowCheck18342 : row18342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18342 := by decide +kernel

theorem rowEval18342 (x : Key → ℝ) : Integer.Sparse.eval row18342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18342, Integer.Sparse.eval_collectBalanced, rawRowCheck18342]

def rawRow18343 : Integer.Sparse Key := [(key2162, 4), (key2162, 4), (key2156, 4), (key2285, -2), (key2285, -2), (key2162, -2), (key2162, -2), (key2156, -2), (key2156, -2), (key2185, -2), (key2185, -2), (key2122, -2), (key2122, -2), (key2114, -2), (key2114, -2), (key2185, 4), (key2185, 4), (key2114, 4)]

theorem rawRowCheck18343 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form17 = rawRow18343 := by decide +kernel

def row18343 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

theorem rowCheck18343 : row18343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18343 := by decide +kernel

theorem rowEval18343 (x : Key → ℝ) : Integer.Sparse.eval row18343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18343, Integer.Sparse.eval_collectBalanced, rawRowCheck18343]

def rawRow18344 : Integer.Sparse Key := [(key2285, 4), (key2285, 4), (key2285, 4), (key2162, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2122, 4), (key2122, 4), (key2122, 4)]

theorem rawRowCheck18344 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form17 = rawRow18344 := by decide +kernel

def row18344 : Integer.Sparse Key := [(key2122, 12), (key2162, -12), (key2185, -12), (key2285, 12)]

theorem rowCheck18344 : row18344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18344 := by decide +kernel

theorem rowEval18344 (x : Key → ℝ) : Integer.Sparse.eval row18344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18344, Integer.Sparse.eval_collectBalanced, rawRowCheck18344]

def rawRow18345 : Integer.Sparse Key := [(key2183, 4), (key2185, 4), (key2185, 4), (key2183, -2), (key2185, -2), (key2183, -2), (key2285, -2), (key2185, -2), (key2285, -2), (key2118, -2), (key2122, -2), (key2118, -2), (key2162, -2), (key2122, -2), (key2162, -2), (key2118, 4), (key2162, 4), (key2162, 4)]

theorem rawRowCheck18345 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form17 = rawRow18345 := by decide +kernel

def row18345 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

theorem rowCheck18345 : row18345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18345 := by decide +kernel

theorem rowEval18345 (x : Key → ℝ) : Integer.Sparse.eval row18345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form17) x := by
  rw [rowCheck18345, Integer.Sparse.eval_collectBalanced, rawRowCheck18345]

def rawRow18346 : Integer.Sparse Key := [(key2185, 4), (key2183, 4), (key2185, 4), (key2185, -2), (key2183, -2), (key2285, -2), (key2183, -2), (key2285, -2), (key2185, -2), (key2122, -2), (key2118, -2), (key2162, -2), (key2118, -2), (key2162, -2), (key2122, -2), (key2162, 4), (key2118, 4), (key2162, 4)]

theorem rawRowCheck18346 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form17 = rawRow18346 := by decide +kernel

def row18346 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

theorem rowCheck18346 : row18346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18346 := by decide +kernel

theorem rowEval18346 (x : Key → ℝ) : Integer.Sparse.eval row18346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18346, Integer.Sparse.eval_collectBalanced, rawRowCheck18346]

def rawRow18347 : Integer.Sparse Key := [(key2185, 4), (key2185, 4), (key2183, 4), (key2285, -2), (key2285, -2), (key2185, -2), (key2185, -2), (key2183, -2), (key2183, -2), (key2162, -2), (key2162, -2), (key2122, -2), (key2122, -2), (key2118, -2), (key2118, -2), (key2162, 4), (key2162, 4), (key2118, 4)]

theorem rawRowCheck18347 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form17 = rawRow18347 := by decide +kernel

def row18347 : Integer.Sparse Key := [(key2122, -4), (key2162, 4), (key2185, 4), (key2285, -4)]

theorem rowCheck18347 : row18347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18347 := by decide +kernel

theorem rowEval18347 (x : Key → ℝ) : Integer.Sparse.eval row18347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18347, Integer.Sparse.eval_collectBalanced, rawRowCheck18347]

def rawRow18348 : Integer.Sparse Key := [(key2285, 4), (key2285, 4), (key2285, 4), (key2185, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2185, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2162, -2), (key2122, 4), (key2122, 4), (key2122, 4)]

theorem rawRowCheck18348 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form17 = rawRow18348 := by decide +kernel

def row18348 : Integer.Sparse Key := [(key2122, 12), (key2162, -12), (key2185, -12), (key2285, 12)]

theorem rowCheck18348 : row18348 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18348 := by decide +kernel

theorem rowEval18348 (x : Key → ℝ) : Integer.Sparse.eval row18348 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form17) x := by
  rw [rowCheck18348, Integer.Sparse.eval_collectBalanced, rawRowCheck18348]

def rawRow18349 : Integer.Sparse Key := [(key2102, -2), (key2104, -2), (key2107, -2), (key2112, -2), (key2110, -2), (key2113, -2), (key2107, 2), (key2112, 2), (key2140, 2), (key2110, 2), (key2113, 2), (key2140, 2), (key2107, 2), (key2112, 2), (key2140, 2), (key2140, -6), (key2110, 2), (key2113, 2), (key2140, 2), (key2140, -6)]

theorem rawRowCheck18349 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form18 = rawRow18349 := by decide +kernel

def row18349 : Integer.Sparse Key := [(key2102, -2), (key2104, -2), (key2107, 2), (key2110, 2), (key2112, 2), (key2113, 2), (key2140, -4)]

theorem rowCheck18349 : row18349 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18349 := by decide +kernel

theorem rowEval18349 (x : Key → ℝ) : Integer.Sparse.eval row18349 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck18349, Integer.Sparse.eval_collectBalanced, rawRowCheck18349]

def rawRow18350 : Integer.Sparse Key := [(key2104, -2), (key2102, -2), (key2112, -2), (key2107, -2), (key2113, -2), (key2110, -2), (key2112, 2), (key2107, 2), (key2140, 2), (key2113, 2), (key2110, 2), (key2140, 2), (key2112, 2), (key2107, 2), (key2140, 2), (key2140, -6), (key2113, 2), (key2110, 2), (key2140, 2), (key2140, -6)]

theorem rawRowCheck18350 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form18 = rawRow18350 := by decide +kernel

def row18350 : Integer.Sparse Key := [(key2102, -2), (key2104, -2), (key2107, 2), (key2110, 2), (key2112, 2), (key2113, 2), (key2140, -4)]

theorem rowCheck18350 : row18350 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18350 := by decide +kernel

theorem rowEval18350 (x : Key → ℝ) : Integer.Sparse.eval row18350 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck18350, Integer.Sparse.eval_collectBalanced, rawRowCheck18350]

def rawRow18351 : Integer.Sparse Key := [(key2107, -2), (key2110, -2), (key2102, -2), (key2113, -2), (key2104, -2), (key2112, -2), (key2107, 2), (key2140, 2), (key2112, 2), (key2110, 2), (key2140, 2), (key2113, 2), (key2107, 2), (key2140, 2), (key2112, 2), (key2140, -6), (key2110, 2), (key2140, 2), (key2113, 2), (key2140, -6)]

theorem rawRowCheck18351 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form18 = rawRow18351 := by decide +kernel

def row18351 : Integer.Sparse Key := [(key2102, -2), (key2104, -2), (key2107, 2), (key2110, 2), (key2112, 2), (key2113, 2), (key2140, -4)]

theorem rowCheck18351 : row18351 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18351 := by decide +kernel

theorem rowEval18351 (x : Key → ℝ) : Integer.Sparse.eval row18351 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck18351, Integer.Sparse.eval_collectBalanced, rawRowCheck18351]

def rawRow18352 : Integer.Sparse Key := [(key2110, -2), (key2107, -2), (key2113, -2), (key2102, -2), (key2112, -2), (key2104, -2), (key2140, 2), (key2107, 2), (key2112, 2), (key2140, 2), (key2110, 2), (key2113, 2), (key2140, 2), (key2107, 2), (key2112, 2), (key2140, -6), (key2140, 2), (key2110, 2), (key2113, 2), (key2140, -6)]

theorem rawRowCheck18352 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form18 = rawRow18352 := by decide +kernel

def row18352 : Integer.Sparse Key := [(key2102, -2), (key2104, -2), (key2107, 2), (key2110, 2), (key2112, 2), (key2113, 2), (key2140, -4)]

theorem rowCheck18352 : row18352 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18352 := by decide +kernel

theorem rowEval18352 (x : Key → ℝ) : Integer.Sparse.eval row18352 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck18352, Integer.Sparse.eval_collectBalanced, rawRowCheck18352]

def rawRow18353 : Integer.Sparse Key := [(key2112, -2), (key2113, -2), (key2104, -2), (key2110, -2), (key2102, -2), (key2107, -2), (key2112, 2), (key2140, 2), (key2107, 2), (key2113, 2), (key2140, 2), (key2110, 2), (key2112, 2), (key2140, 2), (key2107, 2), (key2140, -6), (key2113, 2), (key2140, 2), (key2110, 2), (key2140, -6)]

theorem rawRowCheck18353 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form18 = rawRow18353 := by decide +kernel

def row18353 : Integer.Sparse Key := [(key2102, -2), (key2104, -2), (key2107, 2), (key2110, 2), (key2112, 2), (key2113, 2), (key2140, -4)]

theorem rowCheck18353 : row18353 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18353 := by decide +kernel

theorem rowEval18353 (x : Key → ℝ) : Integer.Sparse.eval row18353 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck18353, Integer.Sparse.eval_collectBalanced, rawRowCheck18353]

def rawRow18354 : Integer.Sparse Key := [(key2113, -2), (key2112, -2), (key2110, -2), (key2104, -2), (key2107, -2), (key2102, -2), (key2140, 2), (key2112, 2), (key2107, 2), (key2140, 2), (key2113, 2), (key2110, 2), (key2140, 2), (key2112, 2), (key2107, 2), (key2140, -6), (key2140, 2), (key2113, 2), (key2110, 2), (key2140, -6)]

theorem rawRowCheck18354 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form18 = rawRow18354 := by decide +kernel

def row18354 : Integer.Sparse Key := [(key2102, -2), (key2104, -2), (key2107, 2), (key2110, 2), (key2112, 2), (key2113, 2), (key2140, -4)]

theorem rowCheck18354 : row18354 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18354 := by decide +kernel

theorem rowEval18354 (x : Key → ℝ) : Integer.Sparse.eval row18354 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck18354, Integer.Sparse.eval_collectBalanced, rawRowCheck18354]

def rawRow18355 : Integer.Sparse Key := [(key2107, -2), (key2110, -2), (key2107, -2), (key2140, -2), (key2110, -2), (key2140, -2), (key2102, 2), (key2113, 2), (key2113, 2), (key2104, 2), (key2112, 2), (key2112, 2), (key2107, 2), (key2140, 2), (key2140, 2), (key2112, -6), (key2110, 2), (key2140, 2), (key2140, 2), (key2113, -6)]

theorem rawRowCheck18355 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form18 = rawRow18355 := by decide +kernel

def row18355 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

theorem rowCheck18355 : row18355 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18355 := by decide +kernel

theorem rowEval18355 (x : Key → ℝ) : Integer.Sparse.eval row18355 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck18355, Integer.Sparse.eval_collectBalanced, rawRowCheck18355]

def rawRow18356 : Integer.Sparse Key := [(key2110, -2), (key2107, -2), (key2140, -2), (key2107, -2), (key2140, -2), (key2110, -2), (key2113, 2), (key2102, 2), (key2113, 2), (key2112, 2), (key2104, 2), (key2112, 2), (key2140, 2), (key2107, 2), (key2140, 2), (key2112, -6), (key2140, 2), (key2110, 2), (key2140, 2), (key2113, -6)]

theorem rawRowCheck18356 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form18 = rawRow18356 := by decide +kernel

def row18356 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

theorem rowCheck18356 : row18356 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18356 := by decide +kernel

theorem rowEval18356 (x : Key → ℝ) : Integer.Sparse.eval row18356 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck18356, Integer.Sparse.eval_collectBalanced, rawRowCheck18356]

def rawRow18357 : Integer.Sparse Key := [(key2140, -2), (key2140, -2), (key2110, -2), (key2110, -2), (key2107, -2), (key2107, -2), (key2113, 2), (key2113, 2), (key2102, 2), (key2112, 2), (key2112, 2), (key2104, 2), (key2140, 2), (key2140, 2), (key2107, 2), (key2112, -6), (key2140, 2), (key2140, 2), (key2110, 2), (key2113, -6)]

theorem rawRowCheck18357 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form18 = rawRow18357 := by decide +kernel

def row18357 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

theorem rowCheck18357 : row18357 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18357 := by decide +kernel

theorem rowEval18357 (x : Key → ℝ) : Integer.Sparse.eval row18357 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck18357, Integer.Sparse.eval_collectBalanced, rawRowCheck18357]

def rawRow18358 : Integer.Sparse Key := [(key2112, -2), (key2113, -2), (key2112, -2), (key2140, -2), (key2113, -2), (key2140, -2), (key2104, 2), (key2110, 2), (key2110, 2), (key2102, 2), (key2107, 2), (key2107, 2), (key2112, 2), (key2140, 2), (key2140, 2), (key2107, -6), (key2113, 2), (key2140, 2), (key2140, 2), (key2110, -6)]

theorem rawRowCheck18358 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form18 = rawRow18358 := by decide +kernel

def row18358 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

theorem rowCheck18358 : row18358 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18358 := by decide +kernel

theorem rowEval18358 (x : Key → ℝ) : Integer.Sparse.eval row18358 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck18358, Integer.Sparse.eval_collectBalanced, rawRowCheck18358]

def rawRow18359 : Integer.Sparse Key := [(key2113, -2), (key2112, -2), (key2140, -2), (key2112, -2), (key2140, -2), (key2113, -2), (key2110, 2), (key2104, 2), (key2110, 2), (key2107, 2), (key2102, 2), (key2107, 2), (key2140, 2), (key2112, 2), (key2140, 2), (key2107, -6), (key2140, 2), (key2113, 2), (key2140, 2), (key2110, -6)]

theorem rawRowCheck18359 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form18 = rawRow18359 := by decide +kernel

def row18359 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

theorem rowCheck18359 : row18359 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18359 := by decide +kernel

theorem rowEval18359 (x : Key → ℝ) : Integer.Sparse.eval row18359 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck18359, Integer.Sparse.eval_collectBalanced, rawRowCheck18359]

def rawRow18360 : Integer.Sparse Key := [(key2140, -2), (key2140, -2), (key2113, -2), (key2113, -2), (key2112, -2), (key2112, -2), (key2110, 2), (key2110, 2), (key2104, 2), (key2107, 2), (key2107, 2), (key2102, 2), (key2140, 2), (key2140, 2), (key2112, 2), (key2107, -6), (key2140, 2), (key2140, 2), (key2113, 2), (key2110, -6)]

theorem rawRowCheck18360 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form18 = rawRow18360 := by decide +kernel

def row18360 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

theorem rowCheck18360 : row18360 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18360 := by decide +kernel

theorem rowEval18360 (x : Key → ℝ) : Integer.Sparse.eval row18360 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck18360, Integer.Sparse.eval_collectBalanced, rawRowCheck18360]

def rawRow18361 : Integer.Sparse Key := [(key2107, -2), (key2110, -2), (key2107, -2), (key2140, -2), (key2110, -2), (key2140, -2), (key2107, 2), (key2140, 2), (key2140, 2), (key2110, 2), (key2140, 2), (key2140, 2), (key2102, 2), (key2113, 2), (key2113, 2), (key2113, -6), (key2104, 2), (key2112, 2), (key2112, 2), (key2112, -6)]

theorem rawRowCheck18361 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form18 = rawRow18361 := by decide +kernel

def row18361 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

theorem rowCheck18361 : row18361 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18361 := by decide +kernel

theorem rowEval18361 (x : Key → ℝ) : Integer.Sparse.eval row18361 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form18) x := by
  rw [rowCheck18361, Integer.Sparse.eval_collectBalanced, rawRowCheck18361]

def rawRow18362 : Integer.Sparse Key := [(key2110, -2), (key2107, -2), (key2140, -2), (key2107, -2), (key2140, -2), (key2110, -2), (key2140, 2), (key2107, 2), (key2140, 2), (key2140, 2), (key2110, 2), (key2140, 2), (key2113, 2), (key2102, 2), (key2113, 2), (key2113, -6), (key2112, 2), (key2104, 2), (key2112, 2), (key2112, -6)]

theorem rawRowCheck18362 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form18 = rawRow18362 := by decide +kernel

def row18362 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

theorem rowCheck18362 : row18362 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18362 := by decide +kernel

theorem rowEval18362 (x : Key → ℝ) : Integer.Sparse.eval row18362 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck18362, Integer.Sparse.eval_collectBalanced, rawRowCheck18362]

def rawRow18363 : Integer.Sparse Key := [(key2140, -2), (key2140, -2), (key2110, -2), (key2110, -2), (key2107, -2), (key2107, -2), (key2140, 2), (key2140, 2), (key2107, 2), (key2140, 2), (key2140, 2), (key2110, 2), (key2113, 2), (key2113, 2), (key2102, 2), (key2113, -6), (key2112, 2), (key2112, 2), (key2104, 2), (key2112, -6)]

theorem rawRowCheck18363 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form18 = rawRow18363 := by decide +kernel

def row18363 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

theorem rowCheck18363 : row18363 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18363 := by decide +kernel

theorem rowEval18363 (x : Key → ℝ) : Integer.Sparse.eval row18363 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck18363, Integer.Sparse.eval_collectBalanced, rawRowCheck18363]

def rawRow18364 : Integer.Sparse Key := [(key2140, -2), (key2140, -2), (key2140, -2), (key2140, -2), (key2140, -2), (key2140, -2), (key2110, 2), (key2110, 2), (key2110, 2), (key2107, 2), (key2107, 2), (key2107, 2), (key2113, 2), (key2113, 2), (key2113, 2), (key2102, -6), (key2112, 2), (key2112, 2), (key2112, 2), (key2104, -6)]

theorem rawRowCheck18364 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form18 = rawRow18364 := by decide +kernel

def row18364 : Integer.Sparse Key := [(key2102, -6), (key2104, -6), (key2107, 6), (key2110, 6), (key2112, 6), (key2113, 6), (key2140, -12)]

theorem rowCheck18364 : row18364 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18364 := by decide +kernel

theorem rowEval18364 (x : Key → ℝ) : Integer.Sparse.eval row18364 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck18364, Integer.Sparse.eval_collectBalanced, rawRowCheck18364]

def rawRow18365 : Integer.Sparse Key := [(key2112, -2), (key2113, -2), (key2112, -2), (key2140, -2), (key2113, -2), (key2140, -2), (key2112, 2), (key2140, 2), (key2140, 2), (key2113, 2), (key2140, 2), (key2140, 2), (key2104, 2), (key2110, 2), (key2110, 2), (key2110, -6), (key2102, 2), (key2107, 2), (key2107, 2), (key2107, -6)]

theorem rawRowCheck18365 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form18 = rawRow18365 := by decide +kernel

def row18365 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

theorem rowCheck18365 : row18365 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18365 := by decide +kernel

theorem rowEval18365 (x : Key → ℝ) : Integer.Sparse.eval row18365 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form18) x := by
  rw [rowCheck18365, Integer.Sparse.eval_collectBalanced, rawRowCheck18365]

def rawRow18366 : Integer.Sparse Key := [(key2113, -2), (key2112, -2), (key2140, -2), (key2112, -2), (key2140, -2), (key2113, -2), (key2140, 2), (key2112, 2), (key2140, 2), (key2140, 2), (key2113, 2), (key2140, 2), (key2110, 2), (key2104, 2), (key2110, 2), (key2110, -6), (key2107, 2), (key2102, 2), (key2107, 2), (key2107, -6)]

theorem rawRowCheck18366 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form18 = rawRow18366 := by decide +kernel

def row18366 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

theorem rowCheck18366 : row18366 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18366 := by decide +kernel

theorem rowEval18366 (x : Key → ℝ) : Integer.Sparse.eval row18366 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck18366, Integer.Sparse.eval_collectBalanced, rawRowCheck18366]

def rawRow18367 : Integer.Sparse Key := [(key2140, -2), (key2140, -2), (key2113, -2), (key2113, -2), (key2112, -2), (key2112, -2), (key2140, 2), (key2140, 2), (key2112, 2), (key2140, 2), (key2140, 2), (key2113, 2), (key2110, 2), (key2110, 2), (key2104, 2), (key2110, -6), (key2107, 2), (key2107, 2), (key2102, 2), (key2107, -6)]

theorem rawRowCheck18367 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form18 = rawRow18367 := by decide +kernel

def row18367 : Integer.Sparse Key := [(key2102, 2), (key2104, 2), (key2107, -2), (key2110, -2), (key2112, -2), (key2113, -2), (key2140, 4)]

theorem rowCheck18367 : row18367 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18367 := by decide +kernel

theorem rowEval18367 (x : Key → ℝ) : Integer.Sparse.eval row18367 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck18367, Integer.Sparse.eval_collectBalanced, rawRowCheck18367]

def rawRow18368 : Integer.Sparse Key := [(key2140, -2), (key2140, -2), (key2140, -2), (key2140, -2), (key2140, -2), (key2140, -2), (key2113, 2), (key2113, 2), (key2113, 2), (key2112, 2), (key2112, 2), (key2112, 2), (key2110, 2), (key2110, 2), (key2110, 2), (key2104, -6), (key2107, 2), (key2107, 2), (key2107, 2), (key2102, -6)]

theorem rawRowCheck18368 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form18 = rawRow18368 := by decide +kernel

def row18368 : Integer.Sparse Key := [(key2102, -6), (key2104, -6), (key2107, 6), (key2110, 6), (key2112, 6), (key2113, 6), (key2140, -12)]

theorem rowCheck18368 : row18368 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18368 := by decide +kernel

theorem rowEval18368 (x : Key → ℝ) : Integer.Sparse.eval row18368 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form18) x := by
  rw [rowCheck18368, Integer.Sparse.eval_collectBalanced, rawRowCheck18368]

def rawRow18369 : Integer.Sparse Key := [(key1945, 4), (key1947, 4), (key1948, 4), (key1947, -4), (key1948, -4), (key1952, -4), (key1947, -4), (key1948, -4), (key1952, -4), (key1952, 12)]

theorem rawRowCheck18369 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form19 = rawRow18369 := by decide +kernel

def row18369 : Integer.Sparse Key := [(key1945, 4), (key1947, -4), (key1948, -4), (key1952, 4)]

theorem rowCheck18369 : row18369 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18369 := by decide +kernel

theorem rowEval18369 (x : Key → ℝ) : Integer.Sparse.eval row18369 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18369, Integer.Sparse.eval_collectBalanced, rawRowCheck18369]

def rawRow18370 : Integer.Sparse Key := [(key1945, 4), (key1948, 4), (key1947, 4), (key1948, -4), (key1947, -4), (key1952, -4), (key1948, -4), (key1947, -4), (key1952, -4), (key1952, 12)]

theorem rawRowCheck18370 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form19 = rawRow18370 := by decide +kernel

def row18370 : Integer.Sparse Key := [(key1945, 4), (key1947, -4), (key1948, -4), (key1952, 4)]

theorem rowCheck18370 : row18370 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18370 := by decide +kernel

theorem rowEval18370 (x : Key → ℝ) : Integer.Sparse.eval row18370 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck18370, Integer.Sparse.eval_collectBalanced, rawRowCheck18370]

def rawRow18371 : Integer.Sparse Key := [(key1947, 4), (key1945, 4), (key1948, 4), (key1947, -4), (key1952, -4), (key1948, -4), (key1947, -4), (key1952, -4), (key1948, -4), (key1952, 12)]

theorem rawRowCheck18371 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form19 = rawRow18371 := by decide +kernel

def row18371 : Integer.Sparse Key := [(key1945, 4), (key1947, -4), (key1948, -4), (key1952, 4)]

theorem rowCheck18371 : row18371 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18371 := by decide +kernel

theorem rowEval18371 (x : Key → ℝ) : Integer.Sparse.eval row18371 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18371, Integer.Sparse.eval_collectBalanced, rawRowCheck18371]

def rawRow18372 : Integer.Sparse Key := [(key1947, 4), (key1948, 4), (key1945, 4), (key1952, -4), (key1947, -4), (key1948, -4), (key1952, -4), (key1947, -4), (key1948, -4), (key1952, 12)]

theorem rawRowCheck18372 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form19 = rawRow18372 := by decide +kernel

def row18372 : Integer.Sparse Key := [(key1945, 4), (key1947, -4), (key1948, -4), (key1952, 4)]

theorem rowCheck18372 : row18372 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18372 := by decide +kernel

theorem rowEval18372 (x : Key → ℝ) : Integer.Sparse.eval row18372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18372, Integer.Sparse.eval_collectBalanced, rawRowCheck18372]

def rawRow18373 : Integer.Sparse Key := [(key1948, 4), (key1945, 4), (key1947, 4), (key1948, -4), (key1952, -4), (key1947, -4), (key1948, -4), (key1952, -4), (key1947, -4), (key1952, 12)]

theorem rawRowCheck18373 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form19 = rawRow18373 := by decide +kernel

def row18373 : Integer.Sparse Key := [(key1945, 4), (key1947, -4), (key1948, -4), (key1952, 4)]

theorem rowCheck18373 : row18373 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18373 := by decide +kernel

theorem rowEval18373 (x : Key → ℝ) : Integer.Sparse.eval row18373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck18373, Integer.Sparse.eval_collectBalanced, rawRowCheck18373]

def rawRow18374 : Integer.Sparse Key := [(key1948, 4), (key1947, 4), (key1945, 4), (key1952, -4), (key1948, -4), (key1947, -4), (key1952, -4), (key1948, -4), (key1947, -4), (key1952, 12)]

theorem rawRowCheck18374 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form19 = rawRow18374 := by decide +kernel

def row18374 : Integer.Sparse Key := [(key1945, 4), (key1947, -4), (key1948, -4), (key1952, 4)]

theorem rowCheck18374 : row18374 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18374 := by decide +kernel

theorem rowEval18374 (x : Key → ℝ) : Integer.Sparse.eval row18374 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18374, Integer.Sparse.eval_collectBalanced, rawRowCheck18374]

def rawRow18375 : Integer.Sparse Key := [(key1947, 4), (key1947, 4), (key1952, 4), (key1945, -4), (key1948, -4), (key1948, -4), (key1947, -4), (key1952, -4), (key1952, -4), (key1948, 12)]

theorem rawRowCheck18375 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form19 = rawRow18375 := by decide +kernel

def row18375 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

theorem rowCheck18375 : row18375 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18375 := by decide +kernel

theorem rowEval18375 (x : Key → ℝ) : Integer.Sparse.eval row18375 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18375, Integer.Sparse.eval_collectBalanced, rawRowCheck18375]

def rawRow18376 : Integer.Sparse Key := [(key1947, 4), (key1952, 4), (key1947, 4), (key1948, -4), (key1945, -4), (key1948, -4), (key1952, -4), (key1947, -4), (key1952, -4), (key1948, 12)]

theorem rawRowCheck18376 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form19 = rawRow18376 := by decide +kernel

def row18376 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

theorem rowCheck18376 : row18376 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18376 := by decide +kernel

theorem rowEval18376 (x : Key → ℝ) : Integer.Sparse.eval row18376 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18376, Integer.Sparse.eval_collectBalanced, rawRowCheck18376]

def rawRow18377 : Integer.Sparse Key := [(key1952, 4), (key1947, 4), (key1947, 4), (key1948, -4), (key1948, -4), (key1945, -4), (key1952, -4), (key1952, -4), (key1947, -4), (key1948, 12)]

theorem rawRowCheck18377 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form19 = rawRow18377 := by decide +kernel

def row18377 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

theorem rowCheck18377 : row18377 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18377 := by decide +kernel

theorem rowEval18377 (x : Key → ℝ) : Integer.Sparse.eval row18377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18377, Integer.Sparse.eval_collectBalanced, rawRowCheck18377]

def rawRow18378 : Integer.Sparse Key := [(key1948, 4), (key1948, 4), (key1952, 4), (key1945, -4), (key1947, -4), (key1947, -4), (key1948, -4), (key1952, -4), (key1952, -4), (key1947, 12)]

theorem rawRowCheck18378 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form19 = rawRow18378 := by decide +kernel

def row18378 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

theorem rowCheck18378 : row18378 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18378 := by decide +kernel

theorem rowEval18378 (x : Key → ℝ) : Integer.Sparse.eval row18378 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck18378, Integer.Sparse.eval_collectBalanced, rawRowCheck18378]

def rawRow18379 : Integer.Sparse Key := [(key1948, 4), (key1952, 4), (key1948, 4), (key1947, -4), (key1945, -4), (key1947, -4), (key1952, -4), (key1948, -4), (key1952, -4), (key1947, 12)]

theorem rawRowCheck18379 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form19 = rawRow18379 := by decide +kernel

def row18379 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

theorem rowCheck18379 : row18379 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18379 := by decide +kernel

theorem rowEval18379 (x : Key → ℝ) : Integer.Sparse.eval row18379 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18379, Integer.Sparse.eval_collectBalanced, rawRowCheck18379]

def rawRow18380 : Integer.Sparse Key := [(key1952, 4), (key1948, 4), (key1948, 4), (key1947, -4), (key1947, -4), (key1945, -4), (key1952, -4), (key1952, -4), (key1948, -4), (key1947, 12)]

theorem rawRowCheck18380 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form19 = rawRow18380 := by decide +kernel

def row18380 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

theorem rowCheck18380 : row18380 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18380 := by decide +kernel

theorem rowEval18380 (x : Key → ℝ) : Integer.Sparse.eval row18380 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18380, Integer.Sparse.eval_collectBalanced, rawRowCheck18380]

def rawRow18381 : Integer.Sparse Key := [(key1947, 4), (key1947, 4), (key1952, 4), (key1947, -4), (key1952, -4), (key1952, -4), (key1945, -4), (key1948, -4), (key1948, -4), (key1948, 12)]

theorem rawRowCheck18381 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form19 = rawRow18381 := by decide +kernel

def row18381 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

theorem rowCheck18381 : row18381 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18381 := by decide +kernel

theorem rowEval18381 (x : Key → ℝ) : Integer.Sparse.eval row18381 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18381, Integer.Sparse.eval_collectBalanced, rawRowCheck18381]

def rawRow18382 : Integer.Sparse Key := [(key1947, 4), (key1952, 4), (key1947, 4), (key1952, -4), (key1947, -4), (key1952, -4), (key1948, -4), (key1945, -4), (key1948, -4), (key1948, 12)]

theorem rawRowCheck18382 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form19 = rawRow18382 := by decide +kernel

def row18382 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

theorem rowCheck18382 : row18382 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18382 := by decide +kernel

theorem rowEval18382 (x : Key → ℝ) : Integer.Sparse.eval row18382 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18382, Integer.Sparse.eval_collectBalanced, rawRowCheck18382]

def rawRow18383 : Integer.Sparse Key := [(key1952, 4), (key1947, 4), (key1947, 4), (key1952, -4), (key1952, -4), (key1947, -4), (key1948, -4), (key1948, -4), (key1945, -4), (key1948, 12)]

theorem rawRowCheck18383 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form19 = rawRow18383 := by decide +kernel

def row18383 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

theorem rowCheck18383 : row18383 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18383 := by decide +kernel

theorem rowEval18383 (x : Key → ℝ) : Integer.Sparse.eval row18383 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18383, Integer.Sparse.eval_collectBalanced, rawRowCheck18383]

def rawRow18384 : Integer.Sparse Key := [(key1952, 4), (key1952, 4), (key1952, 4), (key1947, -4), (key1947, -4), (key1947, -4), (key1948, -4), (key1948, -4), (key1948, -4), (key1945, 12)]

theorem rawRowCheck18384 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form19 = rawRow18384 := by decide +kernel

def row18384 : Integer.Sparse Key := [(key1945, 12), (key1947, -12), (key1948, -12), (key1952, 12)]

theorem rowCheck18384 : row18384 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18384 := by decide +kernel

theorem rowEval18384 (x : Key → ℝ) : Integer.Sparse.eval row18384 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18384, Integer.Sparse.eval_collectBalanced, rawRowCheck18384]

def rawRow18385 : Integer.Sparse Key := [(key1948, 4), (key1948, 4), (key1952, 4), (key1948, -4), (key1952, -4), (key1952, -4), (key1945, -4), (key1947, -4), (key1947, -4), (key1947, 12)]

theorem rawRowCheck18385 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form19 = rawRow18385 := by decide +kernel

def row18385 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

theorem rowCheck18385 : row18385 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18385 := by decide +kernel

theorem rowEval18385 (x : Key → ℝ) : Integer.Sparse.eval row18385 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form19) x := by
  rw [rowCheck18385, Integer.Sparse.eval_collectBalanced, rawRowCheck18385]

def rawRow18386 : Integer.Sparse Key := [(key1948, 4), (key1952, 4), (key1948, 4), (key1952, -4), (key1948, -4), (key1952, -4), (key1947, -4), (key1945, -4), (key1947, -4), (key1947, 12)]

theorem rawRowCheck18386 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form19 = rawRow18386 := by decide +kernel

def row18386 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

theorem rowCheck18386 : row18386 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18386 := by decide +kernel

theorem rowEval18386 (x : Key → ℝ) : Integer.Sparse.eval row18386 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18386, Integer.Sparse.eval_collectBalanced, rawRowCheck18386]

def rawRow18387 : Integer.Sparse Key := [(key1952, 4), (key1948, 4), (key1948, 4), (key1952, -4), (key1952, -4), (key1948, -4), (key1947, -4), (key1947, -4), (key1945, -4), (key1947, 12)]

theorem rawRowCheck18387 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form19 = rawRow18387 := by decide +kernel

def row18387 : Integer.Sparse Key := [(key1945, -4), (key1947, 4), (key1948, 4), (key1952, -4)]

theorem rowCheck18387 : row18387 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18387 := by decide +kernel

theorem rowEval18387 (x : Key → ℝ) : Integer.Sparse.eval row18387 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18387, Integer.Sparse.eval_collectBalanced, rawRowCheck18387]

def rawRow18388 : Integer.Sparse Key := [(key1952, 4), (key1952, 4), (key1952, 4), (key1948, -4), (key1948, -4), (key1948, -4), (key1947, -4), (key1947, -4), (key1947, -4), (key1945, 12)]

theorem rawRowCheck18388 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form19 = rawRow18388 := by decide +kernel

def row18388 : Integer.Sparse Key := [(key1945, 12), (key1947, -12), (key1948, -12), (key1952, 12)]

theorem rowCheck18388 : row18388 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18388 := by decide +kernel

theorem rowEval18388 (x : Key → ℝ) : Integer.Sparse.eval row18388 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18388, Integer.Sparse.eval_collectBalanced, rawRowCheck18388]

def rawRow18389 : Integer.Sparse Key := [(key2117, 4), (key2119, 4), (key2123, 4), (key2117, -2), (key2119, -2), (key2159, -2), (key2184, -2), (key2163, -2), (key2186, -2), (key2117, -2), (key2119, -2), (key2159, -2), (key2184, -2), (key2163, -2), (key2186, -2), (key2159, 4), (key2184, 4), (key2286, 4)]

theorem rawRowCheck18389 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form20 = rawRow18389 := by decide +kernel

def row18389 : Integer.Sparse Key := [(key2123, 4), (key2163, -4), (key2186, -4), (key2286, 4)]

theorem rowCheck18389 : row18389 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18389 := by decide +kernel

theorem rowEval18389 (x : Key → ℝ) : Integer.Sparse.eval row18389 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18389, Integer.Sparse.eval_collectBalanced, rawRowCheck18389]

def rawRow18390 : Integer.Sparse Key := [(key2119, 4), (key2117, 4), (key2123, 4), (key2119, -2), (key2117, -2), (key2184, -2), (key2159, -2), (key2186, -2), (key2163, -2), (key2119, -2), (key2117, -2), (key2184, -2), (key2159, -2), (key2186, -2), (key2163, -2), (key2184, 4), (key2159, 4), (key2286, 4)]

theorem rawRowCheck18390 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form20 = rawRow18390 := by decide +kernel

def row18390 : Integer.Sparse Key := [(key2123, 4), (key2163, -4), (key2186, -4), (key2286, 4)]

theorem rowCheck18390 : row18390 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18390 := by decide +kernel

theorem rowEval18390 (x : Key → ℝ) : Integer.Sparse.eval row18390 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck18390, Integer.Sparse.eval_collectBalanced, rawRowCheck18390]

def rawRow18391 : Integer.Sparse Key := [(key2117, 4), (key2123, 4), (key2119, 4), (key2159, -2), (key2163, -2), (key2117, -2), (key2186, -2), (key2119, -2), (key2184, -2), (key2159, -2), (key2163, -2), (key2117, -2), (key2186, -2), (key2119, -2), (key2184, -2), (key2159, 4), (key2286, 4), (key2184, 4)]

theorem rawRowCheck18391 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form20 = rawRow18391 := by decide +kernel

def row18391 : Integer.Sparse Key := [(key2123, 4), (key2163, -4), (key2186, -4), (key2286, 4)]

theorem rowCheck18391 : row18391 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18391 := by decide +kernel

theorem rowEval18391 (x : Key → ℝ) : Integer.Sparse.eval row18391 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18391, Integer.Sparse.eval_collectBalanced, rawRowCheck18391]

def rawRow18392 : Integer.Sparse Key := [(key2123, 4), (key2117, 4), (key2119, 4), (key2163, -2), (key2159, -2), (key2186, -2), (key2117, -2), (key2184, -2), (key2119, -2), (key2163, -2), (key2159, -2), (key2186, -2), (key2117, -2), (key2184, -2), (key2119, -2), (key2286, 4), (key2159, 4), (key2184, 4)]

theorem rawRowCheck18392 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form20 = rawRow18392 := by decide +kernel

def row18392 : Integer.Sparse Key := [(key2123, 4), (key2163, -4), (key2186, -4), (key2286, 4)]

theorem rowCheck18392 : row18392 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18392 := by decide +kernel

theorem rowEval18392 (x : Key → ℝ) : Integer.Sparse.eval row18392 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18392, Integer.Sparse.eval_collectBalanced, rawRowCheck18392]

def rawRow18393 : Integer.Sparse Key := [(key2119, 4), (key2123, 4), (key2117, 4), (key2184, -2), (key2186, -2), (key2119, -2), (key2163, -2), (key2117, -2), (key2159, -2), (key2184, -2), (key2186, -2), (key2119, -2), (key2163, -2), (key2117, -2), (key2159, -2), (key2184, 4), (key2286, 4), (key2159, 4)]

theorem rawRowCheck18393 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form20 = rawRow18393 := by decide +kernel

def row18393 : Integer.Sparse Key := [(key2123, 4), (key2163, -4), (key2186, -4), (key2286, 4)]

theorem rowCheck18393 : row18393 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18393 := by decide +kernel

theorem rowEval18393 (x : Key → ℝ) : Integer.Sparse.eval row18393 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck18393, Integer.Sparse.eval_collectBalanced, rawRowCheck18393]

def rawRow18394 : Integer.Sparse Key := [(key2123, 4), (key2119, 4), (key2117, 4), (key2186, -2), (key2184, -2), (key2163, -2), (key2119, -2), (key2159, -2), (key2117, -2), (key2186, -2), (key2184, -2), (key2163, -2), (key2119, -2), (key2159, -2), (key2117, -2), (key2286, 4), (key2184, 4), (key2159, 4)]

theorem rawRowCheck18394 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form20 = rawRow18394 := by decide +kernel

def row18394 : Integer.Sparse Key := [(key2123, 4), (key2163, -4), (key2186, -4), (key2286, 4)]

theorem rowCheck18394 : row18394 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18394 := by decide +kernel

theorem rowEval18394 (x : Key → ℝ) : Integer.Sparse.eval row18394 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18394, Integer.Sparse.eval_collectBalanced, rawRowCheck18394]

def rawRow18395 : Integer.Sparse Key := [(key2159, 4), (key2163, 4), (key2163, 4), (key2117, -2), (key2123, -2), (key2117, -2), (key2186, -2), (key2123, -2), (key2186, -2), (key2159, -2), (key2163, -2), (key2159, -2), (key2286, -2), (key2163, -2), (key2286, -2), (key2117, 4), (key2186, 4), (key2186, 4)]

theorem rawRowCheck18395 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form20 = rawRow18395 := by decide +kernel

def row18395 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

theorem rowCheck18395 : row18395 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18395 := by decide +kernel

theorem rowEval18395 (x : Key → ℝ) : Integer.Sparse.eval row18395 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18395, Integer.Sparse.eval_collectBalanced, rawRowCheck18395]

def rawRow18396 : Integer.Sparse Key := [(key2163, 4), (key2159, 4), (key2163, 4), (key2123, -2), (key2117, -2), (key2186, -2), (key2117, -2), (key2186, -2), (key2123, -2), (key2163, -2), (key2159, -2), (key2286, -2), (key2159, -2), (key2286, -2), (key2163, -2), (key2186, 4), (key2117, 4), (key2186, 4)]

theorem rawRowCheck18396 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form20 = rawRow18396 := by decide +kernel

def row18396 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

theorem rowCheck18396 : row18396 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18396 := by decide +kernel

theorem rowEval18396 (x : Key → ℝ) : Integer.Sparse.eval row18396 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18396, Integer.Sparse.eval_collectBalanced, rawRowCheck18396]

def rawRow18397 : Integer.Sparse Key := [(key2163, 4), (key2163, 4), (key2159, 4), (key2186, -2), (key2186, -2), (key2123, -2), (key2123, -2), (key2117, -2), (key2117, -2), (key2286, -2), (key2286, -2), (key2163, -2), (key2163, -2), (key2159, -2), (key2159, -2), (key2186, 4), (key2186, 4), (key2117, 4)]

theorem rawRowCheck18397 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form20 = rawRow18397 := by decide +kernel

def row18397 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

theorem rowCheck18397 : row18397 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18397 := by decide +kernel

theorem rowEval18397 (x : Key → ℝ) : Integer.Sparse.eval row18397 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18397, Integer.Sparse.eval_collectBalanced, rawRowCheck18397]

def rawRow18398 : Integer.Sparse Key := [(key2184, 4), (key2186, 4), (key2186, 4), (key2119, -2), (key2123, -2), (key2119, -2), (key2163, -2), (key2123, -2), (key2163, -2), (key2184, -2), (key2186, -2), (key2184, -2), (key2286, -2), (key2186, -2), (key2286, -2), (key2119, 4), (key2163, 4), (key2163, 4)]

theorem rawRowCheck18398 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form20 = rawRow18398 := by decide +kernel

def row18398 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

theorem rowCheck18398 : row18398 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18398 := by decide +kernel

theorem rowEval18398 (x : Key → ℝ) : Integer.Sparse.eval row18398 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck18398, Integer.Sparse.eval_collectBalanced, rawRowCheck18398]

def rawRow18399 : Integer.Sparse Key := [(key2186, 4), (key2184, 4), (key2186, 4), (key2123, -2), (key2119, -2), (key2163, -2), (key2119, -2), (key2163, -2), (key2123, -2), (key2186, -2), (key2184, -2), (key2286, -2), (key2184, -2), (key2286, -2), (key2186, -2), (key2163, 4), (key2119, 4), (key2163, 4)]

theorem rawRowCheck18399 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form20 = rawRow18399 := by decide +kernel

def row18399 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

theorem rowCheck18399 : row18399 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18399 := by decide +kernel

theorem rowEval18399 (x : Key → ℝ) : Integer.Sparse.eval row18399 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18399, Integer.Sparse.eval_collectBalanced, rawRowCheck18399]

def rawRow18400 : Integer.Sparse Key := [(key2186, 4), (key2186, 4), (key2184, 4), (key2163, -2), (key2163, -2), (key2123, -2), (key2123, -2), (key2119, -2), (key2119, -2), (key2286, -2), (key2286, -2), (key2186, -2), (key2186, -2), (key2184, -2), (key2184, -2), (key2163, 4), (key2163, 4), (key2119, 4)]

theorem rawRowCheck18400 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form20 = rawRow18400 := by decide +kernel

def row18400 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

theorem rowCheck18400 : row18400 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18400 := by decide +kernel

theorem rowEval18400 (x : Key → ℝ) : Integer.Sparse.eval row18400 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18400, Integer.Sparse.eval_collectBalanced, rawRowCheck18400]

def rawRow18401 : Integer.Sparse Key := [(key2159, 4), (key2163, 4), (key2163, 4), (key2159, -2), (key2163, -2), (key2159, -2), (key2286, -2), (key2163, -2), (key2286, -2), (key2117, -2), (key2123, -2), (key2117, -2), (key2186, -2), (key2123, -2), (key2186, -2), (key2117, 4), (key2186, 4), (key2186, 4)]

theorem rawRowCheck18401 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form20 = rawRow18401 := by decide +kernel

def row18401 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

theorem rowCheck18401 : row18401 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18401 := by decide +kernel

theorem rowEval18401 (x : Key → ℝ) : Integer.Sparse.eval row18401 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18401, Integer.Sparse.eval_collectBalanced, rawRowCheck18401]

def rawRow18402 : Integer.Sparse Key := [(key2163, 4), (key2159, 4), (key2163, 4), (key2163, -2), (key2159, -2), (key2286, -2), (key2159, -2), (key2286, -2), (key2163, -2), (key2123, -2), (key2117, -2), (key2186, -2), (key2117, -2), (key2186, -2), (key2123, -2), (key2186, 4), (key2117, 4), (key2186, 4)]

theorem rawRowCheck18402 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form20 = rawRow18402 := by decide +kernel

def row18402 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

theorem rowCheck18402 : row18402 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18402 := by decide +kernel

theorem rowEval18402 (x : Key → ℝ) : Integer.Sparse.eval row18402 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18402, Integer.Sparse.eval_collectBalanced, rawRowCheck18402]

def rawRow18403 : Integer.Sparse Key := [(key2163, 4), (key2163, 4), (key2159, 4), (key2286, -2), (key2286, -2), (key2163, -2), (key2163, -2), (key2159, -2), (key2159, -2), (key2186, -2), (key2186, -2), (key2123, -2), (key2123, -2), (key2117, -2), (key2117, -2), (key2186, 4), (key2186, 4), (key2117, 4)]

theorem rawRowCheck18403 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form20 = rawRow18403 := by decide +kernel

def row18403 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

theorem rowCheck18403 : row18403 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18403 := by decide +kernel

theorem rowEval18403 (x : Key → ℝ) : Integer.Sparse.eval row18403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18403, Integer.Sparse.eval_collectBalanced, rawRowCheck18403]

def rawRow18404 : Integer.Sparse Key := [(key2286, 4), (key2286, 4), (key2286, 4), (key2163, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2123, 4), (key2123, 4), (key2123, 4)]

theorem rawRowCheck18404 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form20 = rawRow18404 := by decide +kernel

def row18404 : Integer.Sparse Key := [(key2123, 12), (key2163, -12), (key2186, -12), (key2286, 12)]

theorem rowCheck18404 : row18404 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18404 := by decide +kernel

theorem rowEval18404 (x : Key → ℝ) : Integer.Sparse.eval row18404 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18404, Integer.Sparse.eval_collectBalanced, rawRowCheck18404]

def rawRow18405 : Integer.Sparse Key := [(key2184, 4), (key2186, 4), (key2186, 4), (key2184, -2), (key2186, -2), (key2184, -2), (key2286, -2), (key2186, -2), (key2286, -2), (key2119, -2), (key2123, -2), (key2119, -2), (key2163, -2), (key2123, -2), (key2163, -2), (key2119, 4), (key2163, 4), (key2163, 4)]

theorem rawRowCheck18405 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form20 = rawRow18405 := by decide +kernel

def row18405 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

theorem rowCheck18405 : row18405 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18405 := by decide +kernel

theorem rowEval18405 (x : Key → ℝ) : Integer.Sparse.eval row18405 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form20) x := by
  rw [rowCheck18405, Integer.Sparse.eval_collectBalanced, rawRowCheck18405]

def rawRow18406 : Integer.Sparse Key := [(key2186, 4), (key2184, 4), (key2186, 4), (key2186, -2), (key2184, -2), (key2286, -2), (key2184, -2), (key2286, -2), (key2186, -2), (key2123, -2), (key2119, -2), (key2163, -2), (key2119, -2), (key2163, -2), (key2123, -2), (key2163, 4), (key2119, 4), (key2163, 4)]

theorem rawRowCheck18406 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form20 = rawRow18406 := by decide +kernel

def row18406 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

theorem rowCheck18406 : row18406 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18406 := by decide +kernel

theorem rowEval18406 (x : Key → ℝ) : Integer.Sparse.eval row18406 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18406, Integer.Sparse.eval_collectBalanced, rawRowCheck18406]

def rawRow18407 : Integer.Sparse Key := [(key2186, 4), (key2186, 4), (key2184, 4), (key2286, -2), (key2286, -2), (key2186, -2), (key2186, -2), (key2184, -2), (key2184, -2), (key2163, -2), (key2163, -2), (key2123, -2), (key2123, -2), (key2119, -2), (key2119, -2), (key2163, 4), (key2163, 4), (key2119, 4)]

theorem rawRowCheck18407 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form20 = rawRow18407 := by decide +kernel

def row18407 : Integer.Sparse Key := [(key2123, -4), (key2163, 4), (key2186, 4), (key2286, -4)]

theorem rowCheck18407 : row18407 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18407 := by decide +kernel

theorem rowEval18407 (x : Key → ℝ) : Integer.Sparse.eval row18407 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18407, Integer.Sparse.eval_collectBalanced, rawRowCheck18407]

def rawRow18408 : Integer.Sparse Key := [(key2286, 4), (key2286, 4), (key2286, 4), (key2186, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2186, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2163, -2), (key2123, 4), (key2123, 4), (key2123, 4)]

theorem rawRowCheck18408 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form20 = rawRow18408 := by decide +kernel

def row18408 : Integer.Sparse Key := [(key2123, 12), (key2163, -12), (key2186, -12), (key2286, 12)]

theorem rowCheck18408 : row18408 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18408 := by decide +kernel

theorem rowEval18408 (x : Key → ℝ) : Integer.Sparse.eval row18408 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form20) x := by
  rw [rowCheck18408, Integer.Sparse.eval_collectBalanced, rawRowCheck18408]

def rawRow18409 : Integer.Sparse Key := [(key3081, -2), (key3082, -2), (key3086, -2), (key3088, -2), (key3090, -2), (key3091, -2), (key3086, 2), (key3088, 2), (key3109, 2), (key3090, 2), (key3091, 2), (key3109, 2), (key3086, 2), (key3088, 2), (key3109, 2), (key3109, -6), (key3090, 2), (key3091, 2), (key3109, 2), (key3109, -6)]

theorem rawRowCheck18409 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form21 = rawRow18409 := by decide +kernel

def row18409 : Integer.Sparse Key := [(key3081, -2), (key3082, -2), (key3086, 2), (key3088, 2), (key3090, 2), (key3091, 2), (key3109, -4)]

theorem rowCheck18409 : row18409 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18409 := by decide +kernel

theorem rowEval18409 (x : Key → ℝ) : Integer.Sparse.eval row18409 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 0, 1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18409, Integer.Sparse.eval_collectBalanced, rawRowCheck18409]

def rawRow18410 : Integer.Sparse Key := [(key3082, -2), (key3081, -2), (key3088, -2), (key3086, -2), (key3091, -2), (key3090, -2), (key3088, 2), (key3086, 2), (key3109, 2), (key3091, 2), (key3090, 2), (key3109, 2), (key3088, 2), (key3086, 2), (key3109, 2), (key3109, -6), (key3091, 2), (key3090, 2), (key3109, 2), (key3109, -6)]

theorem rawRowCheck18410 : GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form21 = rawRow18410 := by decide +kernel

def row18410 : Integer.Sparse Key := [(key3081, -2), (key3082, -2), (key3086, 2), (key3088, 2), (key3090, 2), (key3091, 2), (key3109, -4)]

theorem rowCheck18410 : row18410 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18410 := by decide +kernel

theorem rowEval18410 (x : Key → ℝ) : Integer.Sparse.eval row18410 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, -1, 1, 0] GramFunctions.Block4.form21) x := by
  rw [rowCheck18410, Integer.Sparse.eval_collectBalanced, rawRowCheck18410]

def rawRow18411 : Integer.Sparse Key := [(key3086, -2), (key3088, -2), (key3081, -2), (key3091, -2), (key3082, -2), (key3088, -2), (key3086, 2), (key3109, 2), (key3088, 2), (key3090, 2), (key3109, 2), (key3091, 2), (key3086, 2), (key3109, 2), (key3088, 2), (key3109, -6), (key3090, 2), (key3109, 2), (key3091, 2), (key3109, -6)]

theorem rawRowCheck18411 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form21 = rawRow18411 := by decide +kernel

def row18411 : Integer.Sparse Key := [(key3081, -2), (key3082, -2), (key3086, 2), (key3090, 4), (key3091, 2), (key3109, -4)]

theorem rowCheck18411 : row18411 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18411 := by decide +kernel

theorem rowEval18411 (x : Key → ℝ) : Integer.Sparse.eval row18411 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, -1, 1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18411, Integer.Sparse.eval_collectBalanced, rawRowCheck18411]

def rawRow18412 : Integer.Sparse Key := [(key3088, -2), (key3086, -2), (key3091, -2), (key3081, -2), (key3088, -2), (key3082, -2), (key3109, 2), (key3086, 2), (key3088, 2), (key3109, 2), (key3090, 2), (key3091, 2), (key3109, 2), (key3086, 2), (key3088, 2), (key3109, -6), (key3109, 2), (key3090, 2), (key3091, 2), (key3109, -6)]

theorem rawRowCheck18412 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form21 = rawRow18412 := by decide +kernel

def row18412 : Integer.Sparse Key := [(key3081, -2), (key3082, -2), (key3086, 2), (key3090, 4), (key3091, 2), (key3109, -4)]

theorem rowCheck18412 : row18412 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18412 := by decide +kernel

theorem rowEval18412 (x : Key → ℝ) : Integer.Sparse.eval row18412 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18412, Integer.Sparse.eval_collectBalanced, rawRowCheck18412]

def rawRow18413 : Integer.Sparse Key := [(key3090, -2), (key3091, -2), (key3082, -2), (key3088, -2), (key3081, -2), (key3086, -2), (key3088, 2), (key3109, 2), (key3086, 2), (key3091, 2), (key3109, 2), (key3090, 2), (key3088, 2), (key3109, 2), (key3086, 2), (key3109, -6), (key3091, 2), (key3109, 2), (key3090, 2), (key3109, -6)]

theorem rawRowCheck18413 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form21 = rawRow18413 := by decide +kernel

def row18413 : Integer.Sparse Key := [(key3081, -2), (key3082, -2), (key3086, 2), (key3088, 2), (key3090, 2), (key3091, 2), (key3109, -4)]

theorem rowCheck18413 : row18413 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18413 := by decide +kernel

theorem rowEval18413 (x : Key → ℝ) : Integer.Sparse.eval row18413 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, -1, 0] GramFunctions.Block4.form21) x := by
  rw [rowCheck18413, Integer.Sparse.eval_collectBalanced, rawRowCheck18413]

def rawRow18414 : Integer.Sparse Key := [(key3091, -2), (key3090, -2), (key3088, -2), (key3082, -2), (key3086, -2), (key3081, -2), (key3109, 2), (key3088, 2), (key3086, 2), (key3109, 2), (key3091, 2), (key3090, 2), (key3109, 2), (key3088, 2), (key3086, 2), (key3109, -6), (key3109, 2), (key3091, 2), (key3090, 2), (key3109, -6)]

theorem rawRowCheck18414 : GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form21 = rawRow18414 := by decide +kernel

def row18414 : Integer.Sparse Key := [(key3081, -2), (key3082, -2), (key3086, 2), (key3088, 2), (key3090, 2), (key3091, 2), (key3109, -4)]

theorem rowCheck18414 : row18414 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18414 := by decide +kernel

theorem rowEval18414 (x : Key → ℝ) : Integer.Sparse.eval row18414 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 1, 0, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18414, Integer.Sparse.eval_collectBalanced, rawRowCheck18414]

def rawRow18415 : Integer.Sparse Key := [(key3086, -2), (key3088, -2), (key3086, -2), (key3109, -2), (key3088, -2), (key3109, -2), (key3081, 2), (key3091, 2), (key3091, 2), (key3082, 2), (key3088, 2), (key3088, 2), (key3086, 2), (key3109, 2), (key3109, 2), (key3088, -6), (key3090, 2), (key3109, 2), (key3109, 2), (key3091, -6)]

theorem rawRowCheck18415 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form21 = rawRow18415 := by decide +kernel

def row18415 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, -6), (key3090, 2), (key3091, -2), (key3109, 4)]

theorem rowCheck18415 : row18415 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18415 := by decide +kernel

theorem rowEval18415 (x : Key → ℝ) : Integer.Sparse.eval row18415 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, -1, 1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18415, Integer.Sparse.eval_collectBalanced, rawRowCheck18415]

def rawRow18416 : Integer.Sparse Key := [(key3088, -2), (key3086, -2), (key3109, -2), (key3086, -2), (key3109, -2), (key3088, -2), (key3091, 2), (key3081, 2), (key3091, 2), (key3088, 2), (key3082, 2), (key3088, 2), (key3109, 2), (key3086, 2), (key3109, 2), (key3088, -6), (key3109, 2), (key3090, 2), (key3109, 2), (key3091, -6)]

theorem rawRowCheck18416 : GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form21 = rawRow18416 := by decide +kernel

def row18416 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, -6), (key3090, 2), (key3091, -2), (key3109, 4)]

theorem rowCheck18416 : row18416 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18416 := by decide +kernel

theorem rowEval18416 (x : Key → ℝ) : Integer.Sparse.eval row18416 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, -1, 1, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18416, Integer.Sparse.eval_collectBalanced, rawRowCheck18416]

def rawRow18417 : Integer.Sparse Key := [(key3109, -2), (key3109, -2), (key3088, -2), (key3088, -2), (key3086, -2), (key3086, -2), (key3091, 2), (key3091, 2), (key3081, 2), (key3088, 2), (key3088, 2), (key3082, 2), (key3109, 2), (key3109, 2), (key3086, 2), (key3088, -6), (key3109, 2), (key3109, 2), (key3090, 2), (key3091, -6)]

theorem rawRowCheck18417 : GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form21 = rawRow18417 := by decide +kernel

def row18417 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, -6), (key3090, 2), (key3091, -2), (key3109, 4)]

theorem rowCheck18417 : row18417 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18417 := by decide +kernel

theorem rowEval18417 (x : Key → ℝ) : Integer.Sparse.eval row18417 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 0, 1, -1, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18417, Integer.Sparse.eval_collectBalanced, rawRowCheck18417]

def rawRow18418 : Integer.Sparse Key := [(key3090, -2), (key3091, -2), (key3090, -2), (key3109, -2), (key3091, -2), (key3109, -2), (key3082, 2), (key3088, 2), (key3088, 2), (key3081, 2), (key3086, 2), (key3086, 2), (key3088, 2), (key3109, 2), (key3109, 2), (key3086, -6), (key3091, 2), (key3109, 2), (key3109, 2), (key3090, -6)]

theorem rawRowCheck18418 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form21 = rawRow18418 := by decide +kernel

def row18418 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, 6), (key3090, -10), (key3091, -2), (key3109, 4)]

theorem rowCheck18418 : row18418 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18418 := by decide +kernel

theorem rowEval18418 (x : Key → ℝ) : Integer.Sparse.eval row18418 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, -1, 0] GramFunctions.Block4.form21) x := by
  rw [rowCheck18418, Integer.Sparse.eval_collectBalanced, rawRowCheck18418]

def rawRow18419 : Integer.Sparse Key := [(key3091, -2), (key3090, -2), (key3109, -2), (key3090, -2), (key3109, -2), (key3091, -2), (key3088, 2), (key3082, 2), (key3088, 2), (key3086, 2), (key3081, 2), (key3086, 2), (key3109, 2), (key3088, 2), (key3109, 2), (key3086, -6), (key3109, 2), (key3091, 2), (key3109, 2), (key3090, -6)]

theorem rawRowCheck18419 : GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form21 = rawRow18419 := by decide +kernel

def row18419 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, 6), (key3090, -10), (key3091, -2), (key3109, 4)]

theorem rowCheck18419 : row18419 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18419 := by decide +kernel

theorem rowEval18419 (x : Key → ℝ) : Integer.Sparse.eval row18419 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, -1, 0, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18419, Integer.Sparse.eval_collectBalanced, rawRowCheck18419]

def rawRow18420 : Integer.Sparse Key := [(key3109, -2), (key3109, -2), (key3091, -2), (key3091, -2), (key3090, -2), (key3090, -2), (key3088, 2), (key3088, 2), (key3082, 2), (key3086, 2), (key3086, 2), (key3081, 2), (key3109, 2), (key3109, 2), (key3088, 2), (key3086, -6), (key3109, 2), (key3109, 2), (key3091, 2), (key3090, -6)]

theorem rawRowCheck18420 : GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form21 = rawRow18420 := by decide +kernel

def row18420 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, 6), (key3090, -10), (key3091, -2), (key3109, 4)]

theorem rowCheck18420 : row18420 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18420 := by decide +kernel

theorem rowEval18420 (x : Key → ℝ) : Integer.Sparse.eval row18420 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, 1, 0, -1, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18420, Integer.Sparse.eval_collectBalanced, rawRowCheck18420]

def rawRow18421 : Integer.Sparse Key := [(key3086, -2), (key3088, -2), (key3086, -2), (key3109, -2), (key3088, -2), (key3109, -2), (key3086, 2), (key3109, 2), (key3109, 2), (key3088, 2), (key3109, 2), (key3109, 2), (key3081, 2), (key3091, 2), (key3091, 2), (key3091, -6), (key3082, 2), (key3088, 2), (key3088, 2), (key3088, -6)]

theorem rawRowCheck18421 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form21 = rawRow18421 := by decide +kernel

def row18421 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, -4), (key3091, -2), (key3109, 4)]

theorem rowCheck18421 : row18421 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18421 := by decide +kernel

theorem rowEval18421 (x : Key → ℝ) : Integer.Sparse.eval row18421 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18421, Integer.Sparse.eval_collectBalanced, rawRowCheck18421]

def rawRow18422 : Integer.Sparse Key := [(key3088, -2), (key3086, -2), (key3109, -2), (key3086, -2), (key3109, -2), (key3088, -2), (key3109, 2), (key3086, 2), (key3109, 2), (key3109, 2), (key3088, 2), (key3109, 2), (key3091, 2), (key3081, 2), (key3091, 2), (key3091, -6), (key3088, 2), (key3082, 2), (key3088, 2), (key3088, -6)]

theorem rawRowCheck18422 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form21 = rawRow18422 := by decide +kernel

def row18422 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, -4), (key3091, -2), (key3109, 4)]

theorem rowCheck18422 : row18422 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18422 := by decide +kernel

theorem rowEval18422 (x : Key → ℝ) : Integer.Sparse.eval row18422 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18422, Integer.Sparse.eval_collectBalanced, rawRowCheck18422]

def rawRow18423 : Integer.Sparse Key := [(key3109, -2), (key3109, -2), (key3088, -2), (key3088, -2), (key3086, -2), (key3086, -2), (key3109, 2), (key3109, 2), (key3086, 2), (key3109, 2), (key3109, 2), (key3088, 2), (key3091, 2), (key3091, 2), (key3081, 2), (key3091, -6), (key3088, 2), (key3088, 2), (key3082, 2), (key3088, -6)]

theorem rawRowCheck18423 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form21 = rawRow18423 := by decide +kernel

def row18423 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, -4), (key3091, -2), (key3109, 4)]

theorem rowCheck18423 : row18423 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18423 := by decide +kernel

theorem rowEval18423 (x : Key → ℝ) : Integer.Sparse.eval row18423 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18423, Integer.Sparse.eval_collectBalanced, rawRowCheck18423]

def rawRow18424 : Integer.Sparse Key := [(key3109, -2), (key3109, -2), (key3109, -2), (key3109, -2), (key3109, -2), (key3109, -2), (key3088, 2), (key3088, 2), (key3088, 2), (key3086, 2), (key3086, 2), (key3086, 2), (key3091, 2), (key3091, 2), (key3091, 2), (key3081, -6), (key3088, 2), (key3088, 2), (key3088, 2), (key3082, -6)]

theorem rawRowCheck18424 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form21 = rawRow18424 := by decide +kernel

def row18424 : Integer.Sparse Key := [(key3081, -6), (key3082, -6), (key3086, 6), (key3088, 12), (key3091, 6), (key3109, -12)]

theorem rowCheck18424 : row18424 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18424 := by decide +kernel

theorem rowEval18424 (x : Key → ℝ) : Integer.Sparse.eval row18424 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18424, Integer.Sparse.eval_collectBalanced, rawRowCheck18424]

def rawRow18425 : Integer.Sparse Key := [(key3090, -2), (key3091, -2), (key3090, -2), (key3109, -2), (key3091, -2), (key3109, -2), (key3090, 2), (key3109, 2), (key3109, 2), (key3091, 2), (key3109, 2), (key3109, 2), (key3082, 2), (key3088, 2), (key3088, 2), (key3088, -6), (key3081, 2), (key3086, 2), (key3086, 2), (key3086, -6)]

theorem rawRowCheck18425 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form21 = rawRow18425 := by decide +kernel

def row18425 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, -2), (key3090, -2), (key3091, -2), (key3109, 4)]

theorem rowCheck18425 : row18425 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18425 := by decide +kernel

theorem rowEval18425 (x : Key → ℝ) : Integer.Sparse.eval row18425 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block4.form21) x := by
  rw [rowCheck18425, Integer.Sparse.eval_collectBalanced, rawRowCheck18425]

def rawRow18426 : Integer.Sparse Key := [(key3091, -2), (key3090, -2), (key3109, -2), (key3090, -2), (key3109, -2), (key3091, -2), (key3109, 2), (key3090, 2), (key3109, 2), (key3109, 2), (key3091, 2), (key3109, 2), (key3088, 2), (key3082, 2), (key3088, 2), (key3088, -6), (key3086, 2), (key3081, 2), (key3086, 2), (key3086, -6)]

theorem rawRowCheck18426 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form21 = rawRow18426 := by decide +kernel

def row18426 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, -2), (key3090, -2), (key3091, -2), (key3109, 4)]

theorem rowCheck18426 : row18426 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18426 := by decide +kernel

theorem rowEval18426 (x : Key → ℝ) : Integer.Sparse.eval row18426 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18426, Integer.Sparse.eval_collectBalanced, rawRowCheck18426]

def rawRow18427 : Integer.Sparse Key := [(key3109, -2), (key3109, -2), (key3091, -2), (key3091, -2), (key3090, -2), (key3090, -2), (key3109, 2), (key3109, 2), (key3090, 2), (key3109, 2), (key3109, 2), (key3091, 2), (key3088, 2), (key3088, 2), (key3082, 2), (key3088, -6), (key3086, 2), (key3086, 2), (key3081, 2), (key3086, -6)]

theorem rawRowCheck18427 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form21 = rawRow18427 := by decide +kernel

def row18427 : Integer.Sparse Key := [(key3081, 2), (key3082, 2), (key3086, -2), (key3088, -2), (key3090, -2), (key3091, -2), (key3109, 4)]

theorem rowCheck18427 : row18427 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18427 := by decide +kernel

theorem rowEval18427 (x : Key → ℝ) : Integer.Sparse.eval row18427 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18427, Integer.Sparse.eval_collectBalanced, rawRowCheck18427]

def rawRow18428 : Integer.Sparse Key := [(key3109, -2), (key3109, -2), (key3109, -2), (key3109, -2), (key3109, -2), (key3109, -2), (key3091, 2), (key3091, 2), (key3091, 2), (key3090, 2), (key3090, 2), (key3090, 2), (key3088, 2), (key3088, 2), (key3088, 2), (key3082, -6), (key3086, 2), (key3086, 2), (key3086, 2), (key3081, -6)]

theorem rawRowCheck18428 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form21 = rawRow18428 := by decide +kernel

def row18428 : Integer.Sparse Key := [(key3081, -6), (key3082, -6), (key3086, 6), (key3088, 6), (key3090, 6), (key3091, 6), (key3109, -12)]

theorem rowCheck18428 : row18428 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18428 := by decide +kernel

theorem rowEval18428 (x : Key → ℝ) : Integer.Sparse.eval row18428 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block4.form21) x := by
  rw [rowCheck18428, Integer.Sparse.eval_collectBalanced, rawRowCheck18428]

def rawRow18429 : Integer.Sparse Key := [(key2353, 6), (key2359, 6), (key2359, 6), (key2359, 6), (key2448, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2566, 6), (key2566, 6), (key2566, 6), (key2578, 6)]

theorem rawRowCheck18429 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form0 = rawRow18429 := by decide +kernel

def row18429 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 18), (key2566, 18), (key2578, 6)]

theorem rowCheck18429 : row18429 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18429 := by decide +kernel

theorem rowEval18429 (x : Key → ℝ) : Integer.Sparse.eval row18429 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck18429, Integer.Sparse.eval_collectBalanced, rawRowCheck18429]

def rawRow18430 : Integer.Sparse Key := [(key2359, 6), (key2353, 6), (key2359, 6), (key2359, 6), (key2454, 6), (key2448, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2515, 6), (key2454, 6), (key2566, 6), (key2566, 6), (key2578, 6), (key2566, 6)]

theorem rawRowCheck18430 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form0 = rawRow18430 := by decide +kernel

def row18430 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 18), (key2566, 18), (key2578, 6)]

theorem rowCheck18430 : row18430 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18430 := by decide +kernel

theorem rowEval18430 (x : Key → ℝ) : Integer.Sparse.eval row18430 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18430, Integer.Sparse.eval_collectBalanced, rawRowCheck18430]

def rawRow18431 : Integer.Sparse Key := [(key2359, 6), (key2359, 6), (key2353, 6), (key2359, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2515, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2448, 6), (key2448, 6), (key2515, 6), (key2454, 6), (key2454, 6), (key2566, 6), (key2578, 6), (key2566, 6), (key2566, 6)]

theorem rawRowCheck18431 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form0 = rawRow18431 := by decide +kernel

def row18431 : Integer.Sparse Key := [(key2353, 6), (key2359, 18), (key2448, 18), (key2454, 36), (key2515, 18), (key2566, 18), (key2578, 6)]

theorem rowCheck18431 : row18431 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow18431 := by decide +kernel

theorem rowEval18431 (x : Key → ℝ) : Integer.Sparse.eval row18431 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck18431, Integer.Sparse.eval_collectBalanced, rawRowCheck18431]

end MUB6.Certificate.GramRows

end OAI
