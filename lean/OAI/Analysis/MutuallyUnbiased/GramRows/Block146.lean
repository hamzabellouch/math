import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block16
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow15616 : Integer.Sparse Key := [(key2875, -2), (key2909, -2), (key2875, -2), (key2988, 6), (key2588, -2), (key2599, -2), (key2588, -2), (key2844, 2), (key2888, 2), (key2767, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2967, -2), (key2930, -2), (key2967, -2), (key2584, 6), (key2840, -2), (key2763, -2), (key2840, -2)]

theorem rawRowCheck15616 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form8 = rawRow15616 := by decide +kernel

def row15616 : Integer.Sparse Key := [(key2584, 6), (key2588, -4), (key2599, -2), (key2763, -2), (key2767, 4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2967, -4), (key2988, 6)]

theorem rowCheck15616 : row15616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15616 := by decide +kernel

theorem rowEval15616 (x : Key → ℝ) : Integer.Sparse.eval row15616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15616, Integer.Sparse.eval_collectBalanced, rawRowCheck15616]

def rawRow15617 : Integer.Sparse Key := [(key2909, -2), (key2875, -2), (key2875, -2), (key2988, 6), (key2599, -2), (key2588, -2), (key2588, -2), (key2888, 2), (key2844, 2), (key2888, 2), (key2767, 2), (key2844, 2), (key2767, 2), (key2967, -2), (key2967, -2), (key2930, -2), (key2584, 6), (key2840, -2), (key2840, -2), (key2763, -2)]

theorem rawRowCheck15617 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form8 = rawRow15617 := by decide +kernel

def row15617 : Integer.Sparse Key := [(key2584, 6), (key2588, -4), (key2599, -2), (key2763, -2), (key2767, 4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, 4), (key2909, -2), (key2930, -2), (key2967, -4), (key2988, 6)]

theorem rowCheck15617 : row15617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15617 := by decide +kernel

theorem rowEval15617 (x : Key → ℝ) : Integer.Sparse.eval row15617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15617, Integer.Sparse.eval_collectBalanced, rawRowCheck15617]

def rawRow15618 : Integer.Sparse Key := [(key2875, -2), (key2875, -2), (key2988, -2), (key2909, 6), (key2767, -2), (key2767, -2), (key2930, -2), (key2588, 2), (key2588, 2), (key2844, 2), (key2844, 2), (key2967, 2), (key2967, 2), (key2599, -2), (key2888, -2), (key2888, -2), (key2763, 6), (key2584, -2), (key2840, -2), (key2840, -2)]

theorem rawRowCheck15618 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form8 = rawRow15618 := by decide +kernel

def row15618 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 6), (key2767, -4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, -2), (key2967, 4), (key2988, -2)]

theorem rowCheck15618 : row15618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15618 := by decide +kernel

theorem rowEval15618 (x : Key → ℝ) : Integer.Sparse.eval row15618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15618, Integer.Sparse.eval_collectBalanced, rawRowCheck15618]

def rawRow15619 : Integer.Sparse Key := [(key2875, -2), (key2988, -2), (key2875, -2), (key2909, 6), (key2767, -2), (key2930, -2), (key2767, -2), (key2844, 2), (key2967, 2), (key2588, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2888, -2), (key2599, -2), (key2888, -2), (key2763, 6), (key2840, -2), (key2584, -2), (key2840, -2)]

theorem rawRowCheck15619 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form8 = rawRow15619 := by decide +kernel

def row15619 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 6), (key2767, -4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, -2), (key2967, 4), (key2988, -2)]

theorem rowCheck15619 : row15619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15619 := by decide +kernel

theorem rowEval15619 (x : Key → ℝ) : Integer.Sparse.eval row15619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15619, Integer.Sparse.eval_collectBalanced, rawRowCheck15619]

def rawRow15620 : Integer.Sparse Key := [(key2988, -2), (key2875, -2), (key2875, -2), (key2909, 6), (key2930, -2), (key2767, -2), (key2767, -2), (key2967, 2), (key2844, 2), (key2967, 2), (key2588, 2), (key2844, 2), (key2588, 2), (key2888, -2), (key2888, -2), (key2599, -2), (key2763, 6), (key2840, -2), (key2840, -2), (key2584, -2)]

theorem rawRowCheck15620 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form8 = rawRow15620 := by decide +kernel

def row15620 : Integer.Sparse Key := [(key2584, -2), (key2588, 4), (key2599, -2), (key2763, 6), (key2767, -4), (key2840, -4), (key2844, 4), (key2875, -4), (key2888, -4), (key2909, 6), (key2930, -2), (key2967, 4), (key2988, -2)]

theorem rowCheck15620 : row15620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15620 := by decide +kernel

theorem rowEval15620 (x : Key → ℝ) : Integer.Sparse.eval row15620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form8) x := by
  rw [rowCheck15620, Integer.Sparse.eval_collectBalanced, rawRowCheck15620]

def rawRow15621 : Integer.Sparse Key := [(key2025, 4), (key2054, 4), (key2054, 4), (key2012, -4), (key2012, -4), (key2041, -4), (key2143, -4), (key2143, -4), (key2227, -4), (key2126, 12)]

theorem rawRowCheck15621 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form9 = rawRow15621 := by decide +kernel

def row15621 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, -4), (key2054, 8), (key2126, 12), (key2143, -8), (key2227, -4)]

theorem rowCheck15621 : row15621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15621 := by decide +kernel

theorem rowEval15621 (x : Key → ℝ) : Integer.Sparse.eval row15621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15621, Integer.Sparse.eval_collectBalanced, rawRowCheck15621]

def rawRow15622 : Integer.Sparse Key := [(key2054, 4), (key2025, 4), (key2054, 4), (key2012, -4), (key2041, -4), (key2012, -4), (key2143, -4), (key2227, -4), (key2143, -4), (key2126, 12)]

theorem rawRowCheck15622 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form9 = rawRow15622 := by decide +kernel

def row15622 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, -4), (key2054, 8), (key2126, 12), (key2143, -8), (key2227, -4)]

theorem rowCheck15622 : row15622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15622 := by decide +kernel

theorem rowEval15622 (x : Key → ℝ) : Integer.Sparse.eval row15622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15622, Integer.Sparse.eval_collectBalanced, rawRowCheck15622]

def rawRow15623 : Integer.Sparse Key := [(key2054, 4), (key2054, 4), (key2025, 4), (key2041, -4), (key2012, -4), (key2012, -4), (key2227, -4), (key2143, -4), (key2143, -4), (key2126, 12)]

theorem rawRowCheck15623 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form9 = rawRow15623 := by decide +kernel

def row15623 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, -4), (key2054, 8), (key2126, 12), (key2143, -8), (key2227, -4)]

theorem rowCheck15623 : row15623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15623 := by decide +kernel

theorem rowEval15623 (x : Key → ℝ) : Integer.Sparse.eval row15623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15623, Integer.Sparse.eval_collectBalanced, rawRowCheck15623]

def rawRow15624 : Integer.Sparse Key := [(key2025, 4), (key2143, 4), (key2143, 4), (key2012, -4), (key2012, -4), (key2126, -4), (key2054, -4), (key2054, -4), (key2227, -4), (key2041, 12)]

theorem rawRowCheck15624 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form9 = rawRow15624 := by decide +kernel

def row15624 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, 12), (key2054, -8), (key2126, -4), (key2143, 8), (key2227, -4)]

theorem rowCheck15624 : row15624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15624 := by decide +kernel

theorem rowEval15624 (x : Key → ℝ) : Integer.Sparse.eval row15624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15624, Integer.Sparse.eval_collectBalanced, rawRowCheck15624]

def rawRow15625 : Integer.Sparse Key := [(key2143, 4), (key2025, 4), (key2143, 4), (key2012, -4), (key2126, -4), (key2012, -4), (key2054, -4), (key2227, -4), (key2054, -4), (key2041, 12)]

theorem rawRowCheck15625 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form9 = rawRow15625 := by decide +kernel

def row15625 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, 12), (key2054, -8), (key2126, -4), (key2143, 8), (key2227, -4)]

theorem rowCheck15625 : row15625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15625 := by decide +kernel

theorem rowEval15625 (x : Key → ℝ) : Integer.Sparse.eval row15625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15625, Integer.Sparse.eval_collectBalanced, rawRowCheck15625]

def rawRow15626 : Integer.Sparse Key := [(key2143, 4), (key2143, 4), (key2025, 4), (key2126, -4), (key2012, -4), (key2012, -4), (key2227, -4), (key2054, -4), (key2054, -4), (key2041, 12)]

theorem rawRowCheck15626 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form9 = rawRow15626 := by decide +kernel

def row15626 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, 12), (key2054, -8), (key2126, -4), (key2143, 8), (key2227, -4)]

theorem rowCheck15626 : row15626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15626 := by decide +kernel

theorem rowEval15626 (x : Key → ℝ) : Integer.Sparse.eval row15626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15626, Integer.Sparse.eval_collectBalanced, rawRowCheck15626]

def rawRow15627 : Integer.Sparse Key := [(key2025, 4), (key2054, 4), (key2054, 4), (key2143, -4), (key2143, -4), (key2227, -4), (key2012, -4), (key2012, -4), (key2041, -4), (key2126, 12)]

theorem rawRowCheck15627 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form9 = rawRow15627 := by decide +kernel

def row15627 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, -4), (key2054, 8), (key2126, 12), (key2143, -8), (key2227, -4)]

theorem rowCheck15627 : row15627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15627 := by decide +kernel

theorem rowEval15627 (x : Key → ℝ) : Integer.Sparse.eval row15627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15627, Integer.Sparse.eval_collectBalanced, rawRowCheck15627]

def rawRow15628 : Integer.Sparse Key := [(key2054, 4), (key2025, 4), (key2054, 4), (key2143, -4), (key2227, -4), (key2143, -4), (key2012, -4), (key2041, -4), (key2012, -4), (key2126, 12)]

theorem rawRowCheck15628 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form9 = rawRow15628 := by decide +kernel

def row15628 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, -4), (key2054, 8), (key2126, 12), (key2143, -8), (key2227, -4)]

theorem rowCheck15628 : row15628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15628 := by decide +kernel

theorem rowEval15628 (x : Key → ℝ) : Integer.Sparse.eval row15628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15628, Integer.Sparse.eval_collectBalanced, rawRowCheck15628]

def rawRow15629 : Integer.Sparse Key := [(key2054, 4), (key2054, 4), (key2025, 4), (key2227, -4), (key2143, -4), (key2143, -4), (key2041, -4), (key2012, -4), (key2012, -4), (key2126, 12)]

theorem rawRowCheck15629 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form9 = rawRow15629 := by decide +kernel

def row15629 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, -4), (key2054, 8), (key2126, 12), (key2143, -8), (key2227, -4)]

theorem rowCheck15629 : row15629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15629 := by decide +kernel

theorem rowEval15629 (x : Key → ℝ) : Integer.Sparse.eval row15629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15629, Integer.Sparse.eval_collectBalanced, rawRowCheck15629]

def rawRow15630 : Integer.Sparse Key := [(key2025, 4), (key2143, 4), (key2143, 4), (key2054, -4), (key2054, -4), (key2227, -4), (key2012, -4), (key2012, -4), (key2126, -4), (key2041, 12)]

theorem rawRowCheck15630 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form9 = rawRow15630 := by decide +kernel

def row15630 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, 12), (key2054, -8), (key2126, -4), (key2143, 8), (key2227, -4)]

theorem rowCheck15630 : row15630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15630 := by decide +kernel

theorem rowEval15630 (x : Key → ℝ) : Integer.Sparse.eval row15630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15630, Integer.Sparse.eval_collectBalanced, rawRowCheck15630]

def rawRow15631 : Integer.Sparse Key := [(key2143, 4), (key2025, 4), (key2143, 4), (key2054, -4), (key2227, -4), (key2054, -4), (key2012, -4), (key2126, -4), (key2012, -4), (key2041, 12)]

theorem rawRowCheck15631 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form9 = rawRow15631 := by decide +kernel

def row15631 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, 12), (key2054, -8), (key2126, -4), (key2143, 8), (key2227, -4)]

theorem rowCheck15631 : row15631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15631 := by decide +kernel

theorem rowEval15631 (x : Key → ℝ) : Integer.Sparse.eval row15631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15631, Integer.Sparse.eval_collectBalanced, rawRowCheck15631]

def rawRow15632 : Integer.Sparse Key := [(key2143, 4), (key2143, 4), (key2025, 4), (key2227, -4), (key2054, -4), (key2054, -4), (key2126, -4), (key2012, -4), (key2012, -4), (key2041, 12)]

theorem rawRowCheck15632 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form9 = rawRow15632 := by decide +kernel

def row15632 : Integer.Sparse Key := [(key2012, -8), (key2025, 4), (key2041, 12), (key2054, -8), (key2126, -4), (key2143, 8), (key2227, -4)]

theorem rowCheck15632 : row15632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15632 := by decide +kernel

theorem rowEval15632 (x : Key → ℝ) : Integer.Sparse.eval row15632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form9) x := by
  rw [rowCheck15632, Integer.Sparse.eval_collectBalanced, rawRowCheck15632]

def rawRow15633 : Integer.Sparse Key := [(key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2736, -1), (key2736, -1), (key2664, 2), (key2699, 2), (key2699, 2), (key2791, -1), (key2791, -1), (key2857, -1), (key2857, -1), (key2896, -1), (key2896, -1), (key2783, 2), (key2783, 2), (key2806, 2), (key2806, 2), (key2894, 2), (key2894, 2), (key2779, -1), (key2779, -1), (key2802, -1), (key2802, -1), (key2852, -1), (key2852, -1), (key2942, 2), (key2975, 2), (key2975, 2), (key2937, -1), (key2937, -1), (key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1)]

theorem rawRowCheck15633 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form10 = rawRow15633 := by decide +kernel

def row15633 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, -2), (key2806, 4), (key2852, -2), (key2857, -2), (key2894, 4), (key2896, -2), (key2937, -2), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, 4)]

theorem rowCheck15633 : row15633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15633 := by decide +kernel

theorem rowEval15633 (x : Key → ℝ) : Integer.Sparse.eval row15633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15633, Integer.Sparse.eval_collectBalanced, rawRowCheck15633]

def rawRow15634 : Integer.Sparse Key := [(key2703, -1), (key2736, -1), (key2668, -1), (key2736, -1), (key2668, -1), (key2703, -1), (key2699, 2), (key2664, 2), (key2699, 2), (key2857, -1), (key2896, -1), (key2791, -1), (key2896, -1), (key2791, -1), (key2857, -1), (key2806, 2), (key2894, 2), (key2783, 2), (key2894, 2), (key2783, 2), (key2806, 2), (key2802, -1), (key2852, -1), (key2779, -1), (key2852, -1), (key2779, -1), (key2802, -1), (key2975, 2), (key2942, 2), (key2975, 2), (key2949, -1), (key2973, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2949, -1)]

theorem rawRowCheck15634 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form10 = rawRow15634 := by decide +kernel

def row15634 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, -2), (key2806, 4), (key2852, -2), (key2857, -2), (key2894, 4), (key2896, -2), (key2937, -2), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, 4)]

theorem rowCheck15634 : row15634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15634 := by decide +kernel

theorem rowEval15634 (x : Key → ℝ) : Integer.Sparse.eval row15634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15634, Integer.Sparse.eval_collectBalanced, rawRowCheck15634]

def rawRow15635 : Integer.Sparse Key := [(key2736, -1), (key2703, -1), (key2736, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2699, 2), (key2699, 2), (key2664, 2), (key2896, -1), (key2857, -1), (key2896, -1), (key2791, -1), (key2857, -1), (key2791, -1), (key2894, 2), (key2806, 2), (key2894, 2), (key2783, 2), (key2806, 2), (key2783, 2), (key2852, -1), (key2802, -1), (key2852, -1), (key2779, -1), (key2802, -1), (key2779, -1), (key2975, 2), (key2975, 2), (key2942, 2), (key2973, -1), (key2949, -1), (key2973, -1), (key2937, -1), (key2949, -1), (key2937, -1)]

theorem rawRowCheck15635 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form10 = rawRow15635 := by decide +kernel

def row15635 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, -2), (key2806, 4), (key2852, -2), (key2857, -2), (key2894, 4), (key2896, -2), (key2937, -2), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, 4)]

theorem rowCheck15635 : row15635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15635 := by decide +kernel

theorem rowEval15635 (x : Key → ℝ) : Integer.Sparse.eval row15635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15635, Integer.Sparse.eval_collectBalanced, rawRowCheck15635]

def rawRow15636 : Integer.Sparse Key := [(key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2949, -1), (key2949, -1), (key2609, 2), (key2802, 2), (key2802, 2), (key2637, -1), (key2637, -1), (key2857, -1), (key2857, -1), (key2975, -1), (key2975, -1), (key2629, 2), (key2629, 2), (key2703, 2), (key2703, 2), (key2973, 2), (key2973, 2), (key2625, -1), (key2625, -1), (key2699, -1), (key2699, -1), (key2852, -1), (key2852, -1), (key2652, 2), (key2896, 2), (key2896, 2), (key2647, -1), (key2647, -1), (key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1)]

theorem rawRowCheck15636 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form10 = rawRow15636 := by decide +kernel

def row15636 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2699, -2), (key2703, 4), (key2736, -2), (key2802, 4), (key2806, -2), (key2852, -2), (key2857, -2), (key2894, -2), (key2896, 4), (key2949, -2), (key2973, 4), (key2975, -2)]

theorem rowCheck15636 : row15636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15636 := by decide +kernel

theorem rowEval15636 (x : Key → ℝ) : Integer.Sparse.eval row15636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15636, Integer.Sparse.eval_collectBalanced, rawRowCheck15636]

def rawRow15637 : Integer.Sparse Key := [(key2806, -1), (key2949, -1), (key2613, -1), (key2949, -1), (key2613, -1), (key2806, -1), (key2802, 2), (key2609, 2), (key2802, 2), (key2857, -1), (key2975, -1), (key2637, -1), (key2975, -1), (key2637, -1), (key2857, -1), (key2703, 2), (key2973, 2), (key2629, 2), (key2973, 2), (key2629, 2), (key2703, 2), (key2699, -1), (key2852, -1), (key2625, -1), (key2852, -1), (key2625, -1), (key2699, -1), (key2896, 2), (key2652, 2), (key2896, 2), (key2736, -1), (key2894, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2736, -1)]

theorem rawRowCheck15637 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form10 = rawRow15637 := by decide +kernel

def row15637 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2699, -2), (key2703, 4), (key2736, -2), (key2802, 4), (key2806, -2), (key2852, -2), (key2857, -2), (key2894, -2), (key2896, 4), (key2949, -2), (key2973, 4), (key2975, -2)]

theorem rowCheck15637 : row15637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15637 := by decide +kernel

theorem rowEval15637 (x : Key → ℝ) : Integer.Sparse.eval row15637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15637, Integer.Sparse.eval_collectBalanced, rawRowCheck15637]

def rawRow15638 : Integer.Sparse Key := [(key2949, -1), (key2806, -1), (key2949, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2802, 2), (key2802, 2), (key2609, 2), (key2975, -1), (key2857, -1), (key2975, -1), (key2637, -1), (key2857, -1), (key2637, -1), (key2973, 2), (key2703, 2), (key2973, 2), (key2629, 2), (key2703, 2), (key2629, 2), (key2852, -1), (key2699, -1), (key2852, -1), (key2625, -1), (key2699, -1), (key2625, -1), (key2896, 2), (key2896, 2), (key2652, 2), (key2894, -1), (key2736, -1), (key2894, -1), (key2647, -1), (key2736, -1), (key2647, -1)]

theorem rawRowCheck15638 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form10 = rawRow15638 := by decide +kernel

def row15638 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2699, -2), (key2703, 4), (key2736, -2), (key2802, 4), (key2806, -2), (key2852, -2), (key2857, -2), (key2894, -2), (key2896, 4), (key2949, -2), (key2973, 4), (key2975, -2)]

theorem rowCheck15638 : row15638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15638 := by decide +kernel

theorem rowEval15638 (x : Key → ℝ) : Integer.Sparse.eval row15638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15638, Integer.Sparse.eval_collectBalanced, rawRowCheck15638]

def rawRow15639 : Integer.Sparse Key := [(key2791, -1), (key2791, -1), (key2857, -1), (key2857, -1), (key2896, -1), (key2896, -1), (key2942, 2), (key2975, 2), (key2975, 2), (key2668, -1), (key2668, -1), (key2703, -1), (key2703, -1), (key2736, -1), (key2736, -1), (key2783, 2), (key2783, 2), (key2806, 2), (key2806, 2), (key2894, 2), (key2894, 2), (key2937, -1), (key2937, -1), (key2949, -1), (key2949, -1), (key2973, -1), (key2973, -1), (key2664, 2), (key2699, 2), (key2699, 2), (key2779, -1), (key2779, -1), (key2802, -1), (key2802, -1), (key2852, -1), (key2852, -1)]

theorem rawRowCheck15639 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form10 = rawRow15639 := by decide +kernel

def row15639 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, -2), (key2806, 4), (key2852, -2), (key2857, -2), (key2894, 4), (key2896, -2), (key2937, -2), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, 4)]

theorem rowCheck15639 : row15639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15639 := by decide +kernel

theorem rowEval15639 (x : Key → ℝ) : Integer.Sparse.eval row15639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15639, Integer.Sparse.eval_collectBalanced, rawRowCheck15639]

def rawRow15640 : Integer.Sparse Key := [(key2857, -1), (key2896, -1), (key2791, -1), (key2896, -1), (key2791, -1), (key2857, -1), (key2975, 2), (key2942, 2), (key2975, 2), (key2703, -1), (key2736, -1), (key2668, -1), (key2736, -1), (key2668, -1), (key2703, -1), (key2806, 2), (key2894, 2), (key2783, 2), (key2894, 2), (key2783, 2), (key2806, 2), (key2949, -1), (key2973, -1), (key2937, -1), (key2973, -1), (key2937, -1), (key2949, -1), (key2699, 2), (key2664, 2), (key2699, 2), (key2802, -1), (key2852, -1), (key2779, -1), (key2852, -1), (key2779, -1), (key2802, -1)]

theorem rawRowCheck15640 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form10 = rawRow15640 := by decide +kernel

def row15640 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, -2), (key2806, 4), (key2852, -2), (key2857, -2), (key2894, 4), (key2896, -2), (key2937, -2), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, 4)]

theorem rowCheck15640 : row15640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15640 := by decide +kernel

theorem rowEval15640 (x : Key → ℝ) : Integer.Sparse.eval row15640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15640, Integer.Sparse.eval_collectBalanced, rawRowCheck15640]

def rawRow15641 : Integer.Sparse Key := [(key2896, -1), (key2857, -1), (key2896, -1), (key2791, -1), (key2857, -1), (key2791, -1), (key2975, 2), (key2975, 2), (key2942, 2), (key2736, -1), (key2703, -1), (key2736, -1), (key2668, -1), (key2703, -1), (key2668, -1), (key2894, 2), (key2806, 2), (key2894, 2), (key2783, 2), (key2806, 2), (key2783, 2), (key2973, -1), (key2949, -1), (key2973, -1), (key2937, -1), (key2949, -1), (key2937, -1), (key2699, 2), (key2699, 2), (key2664, 2), (key2852, -1), (key2802, -1), (key2852, -1), (key2779, -1), (key2802, -1), (key2779, -1)]

theorem rawRowCheck15641 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form10 = rawRow15641 := by decide +kernel

def row15641 : Integer.Sparse Key := [(key2664, 2), (key2668, -2), (key2699, 4), (key2703, -2), (key2736, -2), (key2779, -2), (key2783, 4), (key2791, -2), (key2802, -2), (key2806, 4), (key2852, -2), (key2857, -2), (key2894, 4), (key2896, -2), (key2937, -2), (key2942, 2), (key2949, -2), (key2973, -2), (key2975, 4)]

theorem rowCheck15641 : row15641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15641 := by decide +kernel

theorem rowEval15641 (x : Key → ℝ) : Integer.Sparse.eval row15641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15641, Integer.Sparse.eval_collectBalanced, rawRowCheck15641]

def rawRow15642 : Integer.Sparse Key := [(key2637, -1), (key2637, -1), (key2857, -1), (key2857, -1), (key2975, -1), (key2975, -1), (key2652, 2), (key2896, 2), (key2896, 2), (key2613, -1), (key2613, -1), (key2806, -1), (key2806, -1), (key2949, -1), (key2949, -1), (key2629, 2), (key2629, 2), (key2703, 2), (key2703, 2), (key2973, 2), (key2973, 2), (key2647, -1), (key2647, -1), (key2736, -1), (key2736, -1), (key2894, -1), (key2894, -1), (key2609, 2), (key2802, 2), (key2802, 2), (key2625, -1), (key2625, -1), (key2699, -1), (key2699, -1), (key2852, -1), (key2852, -1)]

theorem rawRowCheck15642 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form10 = rawRow15642 := by decide +kernel

def row15642 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2699, -2), (key2703, 4), (key2736, -2), (key2802, 4), (key2806, -2), (key2852, -2), (key2857, -2), (key2894, -2), (key2896, 4), (key2949, -2), (key2973, 4), (key2975, -2)]

theorem rowCheck15642 : row15642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15642 := by decide +kernel

theorem rowEval15642 (x : Key → ℝ) : Integer.Sparse.eval row15642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15642, Integer.Sparse.eval_collectBalanced, rawRowCheck15642]

def rawRow15643 : Integer.Sparse Key := [(key2857, -1), (key2975, -1), (key2637, -1), (key2975, -1), (key2637, -1), (key2857, -1), (key2896, 2), (key2652, 2), (key2896, 2), (key2806, -1), (key2949, -1), (key2613, -1), (key2949, -1), (key2613, -1), (key2806, -1), (key2703, 2), (key2973, 2), (key2629, 2), (key2973, 2), (key2629, 2), (key2703, 2), (key2736, -1), (key2894, -1), (key2647, -1), (key2894, -1), (key2647, -1), (key2736, -1), (key2802, 2), (key2609, 2), (key2802, 2), (key2699, -1), (key2852, -1), (key2625, -1), (key2852, -1), (key2625, -1), (key2699, -1)]

theorem rawRowCheck15643 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form10 = rawRow15643 := by decide +kernel

def row15643 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2699, -2), (key2703, 4), (key2736, -2), (key2802, 4), (key2806, -2), (key2852, -2), (key2857, -2), (key2894, -2), (key2896, 4), (key2949, -2), (key2973, 4), (key2975, -2)]

theorem rowCheck15643 : row15643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15643 := by decide +kernel

theorem rowEval15643 (x : Key → ℝ) : Integer.Sparse.eval row15643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15643, Integer.Sparse.eval_collectBalanced, rawRowCheck15643]

def rawRow15644 : Integer.Sparse Key := [(key2975, -1), (key2857, -1), (key2975, -1), (key2637, -1), (key2857, -1), (key2637, -1), (key2896, 2), (key2896, 2), (key2652, 2), (key2949, -1), (key2806, -1), (key2949, -1), (key2613, -1), (key2806, -1), (key2613, -1), (key2973, 2), (key2703, 2), (key2973, 2), (key2629, 2), (key2703, 2), (key2629, 2), (key2894, -1), (key2736, -1), (key2894, -1), (key2647, -1), (key2736, -1), (key2647, -1), (key2802, 2), (key2802, 2), (key2609, 2), (key2852, -1), (key2699, -1), (key2852, -1), (key2625, -1), (key2699, -1), (key2625, -1)]

theorem rawRowCheck15644 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form10 = rawRow15644 := by decide +kernel

def row15644 : Integer.Sparse Key := [(key2609, 2), (key2613, -2), (key2625, -2), (key2629, 4), (key2637, -2), (key2647, -2), (key2652, 2), (key2699, -2), (key2703, 4), (key2736, -2), (key2802, 4), (key2806, -2), (key2852, -2), (key2857, -2), (key2894, -2), (key2896, 4), (key2949, -2), (key2973, 4), (key2975, -2)]

theorem rowCheck15644 : row15644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15644 := by decide +kernel

theorem rowEval15644 (x : Key → ℝ) : Integer.Sparse.eval row15644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form10) x := by
  rw [rowCheck15644, Integer.Sparse.eval_collectBalanced, rawRowCheck15644]

def rawRow15645 : Integer.Sparse Key := [(key1364, -2), (key1364, -2), (key1374, -2), (key1358, 6), (key1937, -2), (key1937, -2), (key1940, -2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1723, 2), (key1723, 2), (key1484, -2), (key1710, -2), (key1710, -2), (key1949, 6), (key1513, -2), (key1741, -2), (key1741, -2)]

theorem rawRowCheck15645 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form11 = rawRow15645 := by decide +kernel

def row15645 : Integer.Sparse Key := [(key1358, 6), (key1364, -4), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1937, -4), (key1940, -2), (key1949, 6)]

theorem rowCheck15645 : row15645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15645 := by decide +kernel

theorem rowEval15645 (x : Key → ℝ) : Integer.Sparse.eval row15645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15645, Integer.Sparse.eval_collectBalanced, rawRowCheck15645]

def rawRow15646 : Integer.Sparse Key := [(key1364, -2), (key1374, -2), (key1364, -2), (key1358, 6), (key1937, -2), (key1940, -2), (key1937, -2), (key1716, 2), (key1723, 2), (key1490, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1710, -2), (key1484, -2), (key1710, -2), (key1949, 6), (key1741, -2), (key1513, -2), (key1741, -2)]

theorem rawRowCheck15646 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form11 = rawRow15646 := by decide +kernel

def row15646 : Integer.Sparse Key := [(key1358, 6), (key1364, -4), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1937, -4), (key1940, -2), (key1949, 6)]

theorem rowCheck15646 : row15646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15646 := by decide +kernel

theorem rowEval15646 (x : Key → ℝ) : Integer.Sparse.eval row15646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15646, Integer.Sparse.eval_collectBalanced, rawRowCheck15646]

def rawRow15647 : Integer.Sparse Key := [(key1374, -2), (key1364, -2), (key1364, -2), (key1358, 6), (key1940, -2), (key1937, -2), (key1937, -2), (key1723, 2), (key1716, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1490, 2), (key1710, -2), (key1710, -2), (key1484, -2), (key1949, 6), (key1741, -2), (key1741, -2), (key1513, -2)]

theorem rawRowCheck15647 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form11 = rawRow15647 := by decide +kernel

def row15647 : Integer.Sparse Key := [(key1358, 6), (key1364, -4), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1937, -4), (key1940, -2), (key1949, 6)]

theorem rowCheck15647 : row15647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15647 := by decide +kernel

theorem rowEval15647 (x : Key → ℝ) : Integer.Sparse.eval row15647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15647, Integer.Sparse.eval_collectBalanced, rawRowCheck15647]

def rawRow15648 : Integer.Sparse Key := [(key1490, -2), (key1490, -2), (key1513, -2), (key1484, 6), (key1937, -2), (key1937, -2), (key1949, -2), (key1364, 2), (key1364, 2), (key1716, 2), (key1716, 2), (key1741, 2), (key1741, 2), (key1358, -2), (key1710, -2), (key1710, -2), (key1940, 6), (key1374, -2), (key1723, -2), (key1723, -2)]

theorem rawRowCheck15648 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form11 = rawRow15648 := by decide +kernel

def row15648 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 6), (key1490, -4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1937, -4), (key1940, 6), (key1949, -2)]

theorem rowCheck15648 : row15648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15648 := by decide +kernel

theorem rowEval15648 (x : Key → ℝ) : Integer.Sparse.eval row15648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15648, Integer.Sparse.eval_collectBalanced, rawRowCheck15648]

def rawRow15649 : Integer.Sparse Key := [(key1490, -2), (key1513, -2), (key1490, -2), (key1484, 6), (key1937, -2), (key1949, -2), (key1937, -2), (key1716, 2), (key1741, 2), (key1364, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1710, -2), (key1358, -2), (key1710, -2), (key1940, 6), (key1723, -2), (key1374, -2), (key1723, -2)]

theorem rawRowCheck15649 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form11 = rawRow15649 := by decide +kernel

def row15649 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 6), (key1490, -4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1937, -4), (key1940, 6), (key1949, -2)]

theorem rowCheck15649 : row15649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15649 := by decide +kernel

theorem rowEval15649 (x : Key → ℝ) : Integer.Sparse.eval row15649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15649, Integer.Sparse.eval_collectBalanced, rawRowCheck15649]

def rawRow15650 : Integer.Sparse Key := [(key1513, -2), (key1490, -2), (key1490, -2), (key1484, 6), (key1949, -2), (key1937, -2), (key1937, -2), (key1741, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1710, -2), (key1710, -2), (key1358, -2), (key1940, 6), (key1723, -2), (key1723, -2), (key1374, -2)]

theorem rawRowCheck15650 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form11 = rawRow15650 := by decide +kernel

def row15650 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 6), (key1490, -4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1937, -4), (key1940, 6), (key1949, -2)]

theorem rowCheck15650 : row15650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15650 := by decide +kernel

theorem rowEval15650 (x : Key → ℝ) : Integer.Sparse.eval row15650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15650, Integer.Sparse.eval_collectBalanced, rawRowCheck15650]

def rawRow15651 : Integer.Sparse Key := [(key1937, -2), (key1937, -2), (key1940, -2), (key1949, 6), (key1364, -2), (key1364, -2), (key1374, -2), (key1490, 2), (key1490, 2), (key1716, 2), (key1716, 2), (key1723, 2), (key1723, 2), (key1513, -2), (key1741, -2), (key1741, -2), (key1358, 6), (key1484, -2), (key1710, -2), (key1710, -2)]

theorem rawRowCheck15651 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form11 = rawRow15651 := by decide +kernel

def row15651 : Integer.Sparse Key := [(key1358, 6), (key1364, -4), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1937, -4), (key1940, -2), (key1949, 6)]

theorem rowCheck15651 : row15651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15651 := by decide +kernel

theorem rowEval15651 (x : Key → ℝ) : Integer.Sparse.eval row15651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15651, Integer.Sparse.eval_collectBalanced, rawRowCheck15651]

def rawRow15652 : Integer.Sparse Key := [(key1937, -2), (key1940, -2), (key1937, -2), (key1949, 6), (key1364, -2), (key1374, -2), (key1364, -2), (key1716, 2), (key1723, 2), (key1490, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1741, -2), (key1513, -2), (key1741, -2), (key1358, 6), (key1710, -2), (key1484, -2), (key1710, -2)]

theorem rawRowCheck15652 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form11 = rawRow15652 := by decide +kernel

def row15652 : Integer.Sparse Key := [(key1358, 6), (key1364, -4), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1937, -4), (key1940, -2), (key1949, 6)]

theorem rowCheck15652 : row15652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15652 := by decide +kernel

theorem rowEval15652 (x : Key → ℝ) : Integer.Sparse.eval row15652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15652, Integer.Sparse.eval_collectBalanced, rawRowCheck15652]

def rawRow15653 : Integer.Sparse Key := [(key1940, -2), (key1937, -2), (key1937, -2), (key1949, 6), (key1374, -2), (key1364, -2), (key1364, -2), (key1723, 2), (key1716, 2), (key1723, 2), (key1490, 2), (key1716, 2), (key1490, 2), (key1741, -2), (key1741, -2), (key1513, -2), (key1358, 6), (key1710, -2), (key1710, -2), (key1484, -2)]

theorem rawRowCheck15653 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form11 = rawRow15653 := by decide +kernel

def row15653 : Integer.Sparse Key := [(key1358, 6), (key1364, -4), (key1374, -2), (key1484, -2), (key1490, 4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, 4), (key1741, -4), (key1937, -4), (key1940, -2), (key1949, 6)]

theorem rowCheck15653 : row15653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15653 := by decide +kernel

theorem rowEval15653 (x : Key → ℝ) : Integer.Sparse.eval row15653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form11) x := by
  rw [rowCheck15653, Integer.Sparse.eval_collectBalanced, rawRowCheck15653]

def rawRow15654 : Integer.Sparse Key := [(key1937, -2), (key1937, -2), (key1949, -2), (key1940, 6), (key1490, -2), (key1490, -2), (key1513, -2), (key1364, 2), (key1364, 2), (key1716, 2), (key1716, 2), (key1741, 2), (key1741, 2), (key1374, -2), (key1723, -2), (key1723, -2), (key1484, 6), (key1358, -2), (key1710, -2), (key1710, -2)]

theorem rawRowCheck15654 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form11 = rawRow15654 := by decide +kernel

def row15654 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 6), (key1490, -4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1937, -4), (key1940, 6), (key1949, -2)]

theorem rowCheck15654 : row15654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15654 := by decide +kernel

theorem rowEval15654 (x : Key → ℝ) : Integer.Sparse.eval row15654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15654, Integer.Sparse.eval_collectBalanced, rawRowCheck15654]

def rawRow15655 : Integer.Sparse Key := [(key1937, -2), (key1949, -2), (key1937, -2), (key1940, 6), (key1490, -2), (key1513, -2), (key1490, -2), (key1716, 2), (key1741, 2), (key1364, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1723, -2), (key1374, -2), (key1723, -2), (key1484, 6), (key1710, -2), (key1358, -2), (key1710, -2)]

theorem rawRowCheck15655 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form11 = rawRow15655 := by decide +kernel

def row15655 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 6), (key1490, -4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1937, -4), (key1940, 6), (key1949, -2)]

theorem rowCheck15655 : row15655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15655 := by decide +kernel

theorem rowEval15655 (x : Key → ℝ) : Integer.Sparse.eval row15655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form11) x := by
  rw [rowCheck15655, Integer.Sparse.eval_collectBalanced, rawRowCheck15655]

def rawRow15656 : Integer.Sparse Key := [(key1949, -2), (key1937, -2), (key1937, -2), (key1940, 6), (key1513, -2), (key1490, -2), (key1490, -2), (key1741, 2), (key1716, 2), (key1741, 2), (key1364, 2), (key1716, 2), (key1364, 2), (key1723, -2), (key1723, -2), (key1374, -2), (key1484, 6), (key1710, -2), (key1710, -2), (key1358, -2)]

theorem rawRowCheck15656 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form11 = rawRow15656 := by decide +kernel

def row15656 : Integer.Sparse Key := [(key1358, -2), (key1364, 4), (key1374, -2), (key1484, 6), (key1490, -4), (key1513, -2), (key1710, -4), (key1716, 4), (key1723, -4), (key1741, 4), (key1937, -4), (key1940, 6), (key1949, -2)]

theorem rowCheck15656 : row15656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15656 := by decide +kernel

theorem rowEval15656 (x : Key → ℝ) : Integer.Sparse.eval row15656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck15656, Integer.Sparse.eval_collectBalanced, rawRowCheck15656]

def rawRow15657 : Integer.Sparse Key := [(key2383, 2), (key2394, 2), (key2394, 2), (key2378, -2), (key2378, -2), (key2390, -2), (key2880, 2), (key2910, 2), (key2910, 2), (key2766, -1), (key2766, -1), (key2843, -1), (key2843, -1), (key2887, -1), (key2887, -1), (key2989, -2), (key2989, -2), (key3002, -2), (key2931, -1), (key2931, -1), (key2968, -1), (key2968, -1), (key2995, -1), (key2995, -1), (key2929, 4), (key2966, 4), (key2966, 4)]

theorem rawRowCheck15657 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form12 = rawRow15657 := by decide +kernel

def row15657 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2766, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2910, 4), (key2929, 4), (key2931, -2), (key2966, 8), (key2968, -2), (key2989, -4), (key2995, -2), (key3002, -2)]

theorem rowCheck15657 : row15657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15657 := by decide +kernel

theorem rowEval15657 (x : Key → ℝ) : Integer.Sparse.eval row15657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15657, Integer.Sparse.eval_collectBalanced, rawRowCheck15657]

def rawRow15658 : Integer.Sparse Key := [(key2394, 2), (key2383, 2), (key2394, 2), (key2378, -2), (key2390, -2), (key2378, -2), (key2910, 2), (key2880, 2), (key2910, 2), (key2843, -1), (key2887, -1), (key2766, -1), (key2887, -1), (key2766, -1), (key2843, -1), (key2989, -2), (key3002, -2), (key2989, -2), (key2968, -1), (key2995, -1), (key2931, -1), (key2995, -1), (key2931, -1), (key2968, -1), (key2966, 4), (key2929, 4), (key2966, 4)]

theorem rawRowCheck15658 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form12 = rawRow15658 := by decide +kernel

def row15658 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2766, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2910, 4), (key2929, 4), (key2931, -2), (key2966, 8), (key2968, -2), (key2989, -4), (key2995, -2), (key3002, -2)]

theorem rowCheck15658 : row15658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15658 := by decide +kernel

theorem rowEval15658 (x : Key → ℝ) : Integer.Sparse.eval row15658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15658, Integer.Sparse.eval_collectBalanced, rawRowCheck15658]

def rawRow15659 : Integer.Sparse Key := [(key2394, 2), (key2394, 2), (key2383, 2), (key2390, -2), (key2378, -2), (key2378, -2), (key2910, 2), (key2910, 2), (key2880, 2), (key2887, -1), (key2843, -1), (key2887, -1), (key2766, -1), (key2843, -1), (key2766, -1), (key3002, -2), (key2989, -2), (key2989, -2), (key2995, -1), (key2968, -1), (key2995, -1), (key2931, -1), (key2968, -1), (key2931, -1), (key2966, 4), (key2966, 4), (key2929, 4)]

theorem rawRowCheck15659 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form12 = rawRow15659 := by decide +kernel

def row15659 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2766, -2), (key2843, -2), (key2880, 2), (key2887, -2), (key2910, 4), (key2929, 4), (key2931, -2), (key2966, 8), (key2968, -2), (key2989, -4), (key2995, -2), (key3002, -2)]

theorem rowCheck15659 : row15659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15659 := by decide +kernel

theorem rowEval15659 (x : Key → ℝ) : Integer.Sparse.eval row15659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15659, Integer.Sparse.eval_collectBalanced, rawRowCheck15659]

def rawRow15660 : Integer.Sparse Key := [(key2411, 2), (key2443, 2), (key2443, 2), (key2406, -2), (key2406, -2), (key2437, -2), (key2880, 2), (key2989, 2), (key2989, 2), (key2587, -1), (key2587, -1), (key2843, -1), (key2843, -1), (key2966, -1), (key2966, -1), (key2910, -2), (key2910, -2), (key3002, -2), (key2600, -1), (key2600, -1), (key2889, -1), (key2889, -1), (key2995, -1), (key2995, -1), (key2598, 4), (key2887, 4), (key2887, 4)]

theorem rawRowCheck15660 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form12 = rawRow15660 := by decide +kernel

def row15660 : Integer.Sparse Key := [(key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2587, -2), (key2598, 4), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, 8), (key2889, -2), (key2910, -4), (key2966, -2), (key2989, 4), (key2995, -2), (key3002, -2)]

theorem rowCheck15660 : row15660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15660 := by decide +kernel

theorem rowEval15660 (x : Key → ℝ) : Integer.Sparse.eval row15660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15660, Integer.Sparse.eval_collectBalanced, rawRowCheck15660]

def rawRow15661 : Integer.Sparse Key := [(key2443, 2), (key2411, 2), (key2443, 2), (key2406, -2), (key2437, -2), (key2406, -2), (key2989, 2), (key2880, 2), (key2989, 2), (key2843, -1), (key2966, -1), (key2587, -1), (key2966, -1), (key2587, -1), (key2843, -1), (key2910, -2), (key3002, -2), (key2910, -2), (key2889, -1), (key2995, -1), (key2600, -1), (key2995, -1), (key2600, -1), (key2889, -1), (key2887, 4), (key2598, 4), (key2887, 4)]

theorem rawRowCheck15661 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form12 = rawRow15661 := by decide +kernel

def row15661 : Integer.Sparse Key := [(key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2587, -2), (key2598, 4), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, 8), (key2889, -2), (key2910, -4), (key2966, -2), (key2989, 4), (key2995, -2), (key3002, -2)]

theorem rowCheck15661 : row15661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15661 := by decide +kernel

theorem rowEval15661 (x : Key → ℝ) : Integer.Sparse.eval row15661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15661, Integer.Sparse.eval_collectBalanced, rawRowCheck15661]

def rawRow15662 : Integer.Sparse Key := [(key2443, 2), (key2443, 2), (key2411, 2), (key2437, -2), (key2406, -2), (key2406, -2), (key2989, 2), (key2989, 2), (key2880, 2), (key2966, -1), (key2843, -1), (key2966, -1), (key2587, -1), (key2843, -1), (key2587, -1), (key3002, -2), (key2910, -2), (key2910, -2), (key2995, -1), (key2889, -1), (key2995, -1), (key2600, -1), (key2889, -1), (key2600, -1), (key2887, 4), (key2887, 4), (key2598, 4)]

theorem rawRowCheck15662 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form12 = rawRow15662 := by decide +kernel

def row15662 : Integer.Sparse Key := [(key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2587, -2), (key2598, 4), (key2600, -2), (key2843, -2), (key2880, 2), (key2887, 8), (key2889, -2), (key2910, -4), (key2966, -2), (key2989, 4), (key2995, -2), (key3002, -2)]

theorem rowCheck15662 : row15662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15662 := by decide +kernel

theorem rowEval15662 (x : Key → ℝ) : Integer.Sparse.eval row15662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15662, Integer.Sparse.eval_collectBalanced, rawRowCheck15662]

def rawRow15663 : Integer.Sparse Key := [(key2569, 2), (key2571, 2), (key2571, 2), (key2576, -2), (key2576, -2), (key2580, -2), (key2383, 2), (key2394, 2), (key2394, 2), (key2443, -1), (key2443, -1), (key2509, -1), (key2509, -1), (key2524, -1), (key2524, -1), (key2378, -2), (key2378, -2), (key2390, -2), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1), (key2480, -1), (key2480, -1), (key2437, 4), (key2503, 4), (key2503, 4)]

theorem rawRowCheck15663 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form12 = rawRow15663 := by decide +kernel

def row15663 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, 4), (key2443, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2509, -2), (key2524, -2), (key2569, 2), (key2571, 4), (key2576, -4), (key2580, -2)]

theorem rowCheck15663 : row15663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15663 := by decide +kernel

theorem rowEval15663 (x : Key → ℝ) : Integer.Sparse.eval row15663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15663, Integer.Sparse.eval_collectBalanced, rawRowCheck15663]

def rawRow15664 : Integer.Sparse Key := [(key2571, 2), (key2569, 2), (key2571, 2), (key2576, -2), (key2580, -2), (key2576, -2), (key2394, 2), (key2383, 2), (key2394, 2), (key2509, -1), (key2524, -1), (key2443, -1), (key2524, -1), (key2443, -1), (key2509, -1), (key2378, -2), (key2390, -2), (key2378, -2), (key2472, -1), (key2480, -1), (key2406, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2503, 4), (key2437, 4), (key2503, 4)]

theorem rawRowCheck15664 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form12 = rawRow15664 := by decide +kernel

def row15664 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, 4), (key2443, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2509, -2), (key2524, -2), (key2569, 2), (key2571, 4), (key2576, -4), (key2580, -2)]

theorem rowCheck15664 : row15664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15664 := by decide +kernel

theorem rowEval15664 (x : Key → ℝ) : Integer.Sparse.eval row15664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15664, Integer.Sparse.eval_collectBalanced, rawRowCheck15664]

def rawRow15665 : Integer.Sparse Key := [(key2571, 2), (key2571, 2), (key2569, 2), (key2580, -2), (key2576, -2), (key2576, -2), (key2394, 2), (key2394, 2), (key2383, 2), (key2524, -1), (key2509, -1), (key2524, -1), (key2443, -1), (key2509, -1), (key2443, -1), (key2390, -2), (key2378, -2), (key2378, -2), (key2480, -1), (key2472, -1), (key2480, -1), (key2406, -1), (key2472, -1), (key2406, -1), (key2503, 4), (key2503, 4), (key2437, 4)]

theorem rawRowCheck15665 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form12 = rawRow15665 := by decide +kernel

def row15665 : Integer.Sparse Key := [(key2378, -4), (key2383, 2), (key2390, -2), (key2394, 4), (key2406, -2), (key2437, 4), (key2443, -2), (key2472, -2), (key2480, -2), (key2503, 8), (key2509, -2), (key2524, -2), (key2569, 2), (key2571, 4), (key2576, -4), (key2580, -2)]

theorem rowCheck15665 : row15665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15665 := by decide +kernel

theorem rowEval15665 (x : Key → ℝ) : Integer.Sparse.eval row15665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form12) x := by
  rw [rowCheck15665, Integer.Sparse.eval_collectBalanced, rawRowCheck15665]

def rawRow15666 : Integer.Sparse Key := [(key2569, 2), (key2576, 2), (key2576, 2), (key2571, -2), (key2571, -2), (key2580, -2), (key2411, 2), (key2443, 2), (key2443, 2), (key2394, -1), (key2394, -1), (key2484, -1), (key2484, -1), (key2524, -1), (key2524, -1), (key2406, -2), (key2406, -2), (key2437, -2), (key2378, -1), (key2378, -1), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2390, 4), (key2480, 4), (key2480, 4)]

theorem rawRowCheck15666 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form12 = rawRow15666 := by decide +kernel

def row15666 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2394, -2), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -2), (key2480, 8), (key2484, -2), (key2503, -2), (key2524, -2), (key2569, 2), (key2571, -4), (key2576, 4), (key2580, -2)]

theorem rowCheck15666 : row15666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15666 := by decide +kernel

theorem rowEval15666 (x : Key → ℝ) : Integer.Sparse.eval row15666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15666, Integer.Sparse.eval_collectBalanced, rawRowCheck15666]

def rawRow15667 : Integer.Sparse Key := [(key2576, 2), (key2569, 2), (key2576, 2), (key2571, -2), (key2580, -2), (key2571, -2), (key2443, 2), (key2411, 2), (key2443, 2), (key2484, -1), (key2524, -1), (key2394, -1), (key2524, -1), (key2394, -1), (key2484, -1), (key2406, -2), (key2437, -2), (key2406, -2), (key2472, -1), (key2503, -1), (key2378, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2480, 4), (key2390, 4), (key2480, 4)]

theorem rawRowCheck15667 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form12 = rawRow15667 := by decide +kernel

def row15667 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2394, -2), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -2), (key2480, 8), (key2484, -2), (key2503, -2), (key2524, -2), (key2569, 2), (key2571, -4), (key2576, 4), (key2580, -2)]

theorem rowCheck15667 : row15667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15667 := by decide +kernel

theorem rowEval15667 (x : Key → ℝ) : Integer.Sparse.eval row15667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck15667, Integer.Sparse.eval_collectBalanced, rawRowCheck15667]

def rawRow15668 : Integer.Sparse Key := [(key2576, 2), (key2576, 2), (key2569, 2), (key2580, -2), (key2571, -2), (key2571, -2), (key2443, 2), (key2443, 2), (key2411, 2), (key2524, -1), (key2484, -1), (key2524, -1), (key2394, -1), (key2484, -1), (key2394, -1), (key2437, -2), (key2406, -2), (key2406, -2), (key2503, -1), (key2472, -1), (key2503, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2480, 4), (key2480, 4), (key2390, 4)]

theorem rawRowCheck15668 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form12 = rawRow15668 := by decide +kernel

def row15668 : Integer.Sparse Key := [(key2378, -2), (key2390, 4), (key2394, -2), (key2406, -4), (key2411, 2), (key2437, -2), (key2443, 4), (key2472, -2), (key2480, 8), (key2484, -2), (key2503, -2), (key2524, -2), (key2569, 2), (key2571, -4), (key2576, 4), (key2580, -2)]

theorem rowCheck15668 : row15668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15668 := by decide +kernel

theorem rowEval15668 (x : Key → ℝ) : Integer.Sparse.eval row15668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form12) x := by
  rw [rowCheck15668, Integer.Sparse.eval_collectBalanced, rawRowCheck15668]

def rawRow15669 : Integer.Sparse Key := [(key2657, 2), (key2657, 2), (key2659, 2), (key2614, -1), (key2614, -1), (key2630, -1), (key2630, -1), (key2638, -1), (key2638, -1), (key2724, 2), (key2724, 2), (key2757, 2), (key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2752, -1), (key2752, -1), (key2827, -1), (key2827, -1), (key2868, -1), (key2868, -1), (key2922, -1), (key2922, -1), (key2792, -1), (key2792, -1), (key2858, -1), (key2858, -1), (key2919, -1), (key2919, -1), (key2784, 2), (key2784, 2), (key2807, 2), (key2807, 2), (key2918, 2), (key2918, 2)]

theorem rawRowCheck15669 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form13 = rawRow15669 := by decide +kernel

def row15669 : Integer.Sparse Key := [(key2614, -2), (key2630, -2), (key2638, -2), (key2657, 4), (key2659, 2), (key2669, -2), (key2704, -2), (key2724, 4), (key2752, -2), (key2757, 2), (key2784, 4), (key2792, -2), (key2807, 4), (key2827, -2), (key2858, -2), (key2868, -2), (key2918, 4), (key2919, -2), (key2922, -2)]

theorem rowCheck15669 : row15669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15669 := by decide +kernel

theorem rowEval15669 (x : Key → ℝ) : Integer.Sparse.eval row15669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15669, Integer.Sparse.eval_collectBalanced, rawRowCheck15669]

def rawRow15670 : Integer.Sparse Key := [(key2657, 2), (key2659, 2), (key2657, 2), (key2630, -1), (key2638, -1), (key2614, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2724, 2), (key2757, 2), (key2724, 2), (key2704, -1), (key2752, -1), (key2669, -1), (key2752, -1), (key2669, -1), (key2704, -1), (key2868, -1), (key2922, -1), (key2827, -1), (key2922, -1), (key2827, -1), (key2868, -1), (key2858, -1), (key2919, -1), (key2792, -1), (key2919, -1), (key2792, -1), (key2858, -1), (key2807, 2), (key2918, 2), (key2784, 2), (key2918, 2), (key2784, 2), (key2807, 2)]

theorem rawRowCheck15670 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form13 = rawRow15670 := by decide +kernel

def row15670 : Integer.Sparse Key := [(key2614, -2), (key2630, -2), (key2638, -2), (key2657, 4), (key2659, 2), (key2669, -2), (key2704, -2), (key2724, 4), (key2752, -2), (key2757, 2), (key2784, 4), (key2792, -2), (key2807, 4), (key2827, -2), (key2858, -2), (key2868, -2), (key2918, 4), (key2919, -2), (key2922, -2)]

theorem rowCheck15670 : row15670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15670 := by decide +kernel

theorem rowEval15670 (x : Key → ℝ) : Integer.Sparse.eval row15670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15670, Integer.Sparse.eval_collectBalanced, rawRowCheck15670]

def rawRow15671 : Integer.Sparse Key := [(key2659, 2), (key2657, 2), (key2657, 2), (key2638, -1), (key2630, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2614, -1), (key2757, 2), (key2724, 2), (key2724, 2), (key2752, -1), (key2704, -1), (key2752, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key2922, -1), (key2868, -1), (key2922, -1), (key2827, -1), (key2868, -1), (key2827, -1), (key2919, -1), (key2858, -1), (key2919, -1), (key2792, -1), (key2858, -1), (key2792, -1), (key2918, 2), (key2807, 2), (key2918, 2), (key2784, 2), (key2807, 2), (key2784, 2)]

theorem rawRowCheck15671 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form13 = rawRow15671 := by decide +kernel

def row15671 : Integer.Sparse Key := [(key2614, -2), (key2630, -2), (key2638, -2), (key2657, 4), (key2659, 2), (key2669, -2), (key2704, -2), (key2724, 4), (key2752, -2), (key2757, 2), (key2784, 4), (key2792, -2), (key2807, 4), (key2827, -2), (key2858, -2), (key2868, -2), (key2918, 4), (key2919, -2), (key2922, -2)]

theorem rowCheck15671 : row15671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15671 := by decide +kernel

theorem rowEval15671 (x : Key → ℝ) : Integer.Sparse.eval row15671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck15671, Integer.Sparse.eval_collectBalanced, rawRowCheck15671]

def rawRow15672 : Integer.Sparse Key := [(key2752, 2), (key2752, 2), (key2757, 2), (key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2724, -1), (key2724, -1), (key3011, 2), (key3011, 2), (key3016, 2), (key2614, -1), (key2614, -1), (key2807, -1), (key2807, -1), (key2827, -1), (key2827, -1), (key2724, -1), (key2724, -1), (key2868, -1), (key2868, -1), (key3025, -1), (key3025, -1), (key2638, -1), (key2638, -1), (key2858, -1), (key2858, -1), (key3022, -1), (key3022, -1), (key2630, 2), (key2630, 2), (key2704, 2), (key2704, 2), (key3021, 2), (key3021, 2)]

theorem rawRowCheck15672 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form13 = rawRow15672 := by decide +kernel

def row15672 : Integer.Sparse Key := [(key2614, -2), (key2630, 4), (key2638, -2), (key2669, -2), (key2704, 2), (key2724, -4), (key2752, 4), (key2757, 2), (key2807, -2), (key2827, -2), (key2858, -2), (key2868, -2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

theorem rowCheck15672 : row15672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15672 := by decide +kernel

theorem rowEval15672 (x : Key → ℝ) : Integer.Sparse.eval row15672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15672, Integer.Sparse.eval_collectBalanced, rawRowCheck15672]

def rawRow15673 : Integer.Sparse Key := [(key2752, 2), (key2757, 2), (key2752, 2), (key2704, -1), (key2724, -1), (key2669, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key3011, 2), (key3016, 2), (key3011, 2), (key2807, -1), (key2827, -1), (key2614, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2868, -1), (key3025, -1), (key2724, -1), (key3025, -1), (key2724, -1), (key2868, -1), (key2858, -1), (key3022, -1), (key2638, -1), (key3022, -1), (key2638, -1), (key2858, -1), (key2704, 2), (key3021, 2), (key2630, 2), (key3021, 2), (key2630, 2), (key2704, 2)]

theorem rawRowCheck15673 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form13 = rawRow15673 := by decide +kernel

def row15673 : Integer.Sparse Key := [(key2614, -2), (key2630, 4), (key2638, -2), (key2669, -2), (key2704, 2), (key2724, -4), (key2752, 4), (key2757, 2), (key2807, -2), (key2827, -2), (key2858, -2), (key2868, -2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

theorem rowCheck15673 : row15673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15673 := by decide +kernel

theorem rowEval15673 (x : Key → ℝ) : Integer.Sparse.eval row15673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15673, Integer.Sparse.eval_collectBalanced, rawRowCheck15673]

def rawRow15674 : Integer.Sparse Key := [(key2757, 2), (key2752, 2), (key2752, 2), (key2724, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key3016, 2), (key3011, 2), (key3011, 2), (key2827, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2614, -1), (key3025, -1), (key2868, -1), (key3025, -1), (key2724, -1), (key2868, -1), (key2724, -1), (key3022, -1), (key2858, -1), (key3022, -1), (key2638, -1), (key2858, -1), (key2638, -1), (key3021, 2), (key2704, 2), (key3021, 2), (key2630, 2), (key2704, 2), (key2630, 2)]

theorem rawRowCheck15674 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form13 = rawRow15674 := by decide +kernel

def row15674 : Integer.Sparse Key := [(key2614, -2), (key2630, 4), (key2638, -2), (key2669, -2), (key2704, 2), (key2724, -4), (key2752, 4), (key2757, 2), (key2807, -2), (key2827, -2), (key2858, -2), (key2868, -2), (key3011, 4), (key3016, 2), (key3021, 4), (key3022, -2), (key3025, -2)]

theorem rowCheck15674 : row15674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15674 := by decide +kernel

theorem rowEval15674 (x : Key → ℝ) : Integer.Sparse.eval row15674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15674, Integer.Sparse.eval_collectBalanced, rawRowCheck15674]

def rawRow15675 : Integer.Sparse Key := [(key3007, 2), (key3007, 2), (key3009, 2), (key3011, -1), (key3011, -1), (key3021, -1), (key3021, -1), (key3022, -1), (key3022, -1), (key2657, 2), (key2657, 2), (key2659, 2), (key2752, -1), (key2752, -1), (key2918, -1), (key2918, -1), (key2919, -1), (key2919, -1), (key2614, -1), (key2614, -1), (key2630, -1), (key2630, -1), (key2638, -1), (key2638, -1), (key2669, -1), (key2669, -1), (key2784, -1), (key2784, -1), (key2792, -1), (key2792, -1), (key2704, 2), (key2704, 2), (key2807, 2), (key2807, 2), (key2858, 2), (key2858, 2)]

theorem rawRowCheck15675 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form13 = rawRow15675 := by decide +kernel

def row15675 : Integer.Sparse Key := [(key2614, -2), (key2630, -2), (key2638, -2), (key2657, 4), (key2659, 2), (key2669, -2), (key2704, 4), (key2752, -2), (key2784, -2), (key2792, -2), (key2807, 4), (key2858, 4), (key2918, -2), (key2919, -2), (key3007, 4), (key3009, 2), (key3011, -2), (key3021, -2), (key3022, -2)]

theorem rowCheck15675 : row15675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15675 := by decide +kernel

theorem rowEval15675 (x : Key → ℝ) : Integer.Sparse.eval row15675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15675, Integer.Sparse.eval_collectBalanced, rawRowCheck15675]

def rawRow15676 : Integer.Sparse Key := [(key3007, 2), (key3009, 2), (key3007, 2), (key3021, -1), (key3022, -1), (key3011, -1), (key3022, -1), (key3011, -1), (key3021, -1), (key2657, 2), (key2659, 2), (key2657, 2), (key2918, -1), (key2919, -1), (key2752, -1), (key2919, -1), (key2752, -1), (key2918, -1), (key2630, -1), (key2638, -1), (key2614, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2784, -1), (key2792, -1), (key2669, -1), (key2792, -1), (key2669, -1), (key2784, -1), (key2807, 2), (key2858, 2), (key2704, 2), (key2858, 2), (key2704, 2), (key2807, 2)]

theorem rawRowCheck15676 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form13 = rawRow15676 := by decide +kernel

def row15676 : Integer.Sparse Key := [(key2614, -2), (key2630, -2), (key2638, -2), (key2657, 4), (key2659, 2), (key2669, -2), (key2704, 4), (key2752, -2), (key2784, -2), (key2792, -2), (key2807, 4), (key2858, 4), (key2918, -2), (key2919, -2), (key3007, 4), (key3009, 2), (key3011, -2), (key3021, -2), (key3022, -2)]

theorem rowCheck15676 : row15676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15676 := by decide +kernel

theorem rowEval15676 (x : Key → ℝ) : Integer.Sparse.eval row15676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15676, Integer.Sparse.eval_collectBalanced, rawRowCheck15676]

def rawRow15677 : Integer.Sparse Key := [(key3009, 2), (key3007, 2), (key3007, 2), (key3022, -1), (key3021, -1), (key3022, -1), (key3011, -1), (key3021, -1), (key3011, -1), (key2659, 2), (key2657, 2), (key2657, 2), (key2919, -1), (key2918, -1), (key2919, -1), (key2752, -1), (key2918, -1), (key2752, -1), (key2638, -1), (key2630, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2614, -1), (key2792, -1), (key2784, -1), (key2792, -1), (key2669, -1), (key2784, -1), (key2669, -1), (key2858, 2), (key2807, 2), (key2858, 2), (key2704, 2), (key2807, 2), (key2704, 2)]

theorem rawRowCheck15677 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form13 = rawRow15677 := by decide +kernel

def row15677 : Integer.Sparse Key := [(key2614, -2), (key2630, -2), (key2638, -2), (key2657, 4), (key2659, 2), (key2669, -2), (key2704, 4), (key2752, -2), (key2784, -2), (key2792, -2), (key2807, 4), (key2858, 4), (key2918, -2), (key2919, -2), (key3007, 4), (key3009, 2), (key3011, -2), (key3021, -2), (key3022, -2)]

theorem rowCheck15677 : row15677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15677 := by decide +kernel

theorem rowEval15677 (x : Key → ℝ) : Integer.Sparse.eval row15677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form13) x := by
  rw [rowCheck15677, Integer.Sparse.eval_collectBalanced, rawRowCheck15677]

def rawRow15678 : Integer.Sparse Key := [(key3011, 2), (key3011, 2), (key3016, 2), (key3007, -1), (key3007, -1), (key3021, -1), (key3021, -1), (key3025, -1), (key3025, -1), (key2752, 2), (key2752, 2), (key2757, 2), (key2657, -1), (key2657, -1), (key2918, -1), (key2918, -1), (key2922, -1), (key2922, -1), (key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2724, -1), (key2724, -1), (key2614, -1), (key2614, -1), (key2807, -1), (key2807, -1), (key2827, -1), (key2827, -1), (key2630, 2), (key2630, 2), (key2784, 2), (key2784, 2), (key2868, 2), (key2868, 2)]

theorem rawRowCheck15678 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form13 = rawRow15678 := by decide +kernel

def row15678 : Integer.Sparse Key := [(key2614, -2), (key2630, 4), (key2657, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2784, 4), (key2807, -2), (key2827, -2), (key2868, 4), (key2918, -2), (key2922, -2), (key3007, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3025, -2)]

theorem rowCheck15678 : row15678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15678 := by decide +kernel

theorem rowEval15678 (x : Key → ℝ) : Integer.Sparse.eval row15678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15678, Integer.Sparse.eval_collectBalanced, rawRowCheck15678]

def rawRow15679 : Integer.Sparse Key := [(key3011, 2), (key3016, 2), (key3011, 2), (key3021, -1), (key3025, -1), (key3007, -1), (key3025, -1), (key3007, -1), (key3021, -1), (key2752, 2), (key2757, 2), (key2752, 2), (key2918, -1), (key2922, -1), (key2657, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2784, 2), (key2868, 2), (key2630, 2), (key2868, 2), (key2630, 2), (key2784, 2)]

theorem rawRowCheck15679 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form13 = rawRow15679 := by decide +kernel

def row15679 : Integer.Sparse Key := [(key2614, -2), (key2630, 4), (key2657, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2784, 4), (key2807, -2), (key2827, -2), (key2868, 4), (key2918, -2), (key2922, -2), (key3007, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3025, -2)]

theorem rowCheck15679 : row15679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15679 := by decide +kernel

theorem rowEval15679 (x : Key → ℝ) : Integer.Sparse.eval row15679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form13) x := by
  rw [rowCheck15679, Integer.Sparse.eval_collectBalanced, rawRowCheck15679]

def rawRow15680 : Integer.Sparse Key := [(key3016, 2), (key3011, 2), (key3011, 2), (key3025, -1), (key3021, -1), (key3025, -1), (key3007, -1), (key3021, -1), (key3007, -1), (key2757, 2), (key2752, 2), (key2752, 2), (key2922, -1), (key2918, -1), (key2922, -1), (key2657, -1), (key2918, -1), (key2657, -1), (key2724, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key2827, -1), (key2807, -1), (key2827, -1), (key2614, -1), (key2807, -1), (key2614, -1), (key2868, 2), (key2784, 2), (key2868, 2), (key2630, 2), (key2784, 2), (key2630, 2)]

theorem rawRowCheck15680 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form13 = rawRow15680 := by decide +kernel

def row15680 : Integer.Sparse Key := [(key2614, -2), (key2630, 4), (key2657, -2), (key2669, -2), (key2704, -2), (key2724, -2), (key2752, 4), (key2757, 2), (key2784, 4), (key2807, -2), (key2827, -2), (key2868, 4), (key2918, -2), (key2922, -2), (key3007, -2), (key3011, 4), (key3016, 2), (key3021, -2), (key3025, -2)]

theorem rowCheck15680 : row15680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15680 := by decide +kernel

theorem rowEval15680 (x : Key → ℝ) : Integer.Sparse.eval row15680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form13) x := by
  rw [rowCheck15680, Integer.Sparse.eval_collectBalanced, rawRowCheck15680]

def rawRow15681 : Integer.Sparse Key := [(key2608, -1), (key2614, -1), (key2624, -1), (key2638, -1), (key2657, -1), (key2659, -1), (key2614, 2), (key2630, 2), (key2638, 2), (key2663, 1), (key2669, 1), (key2698, 1), (key2724, 1), (key2752, 1), (key2757, 1), (key2669, -2), (key2704, -2), (key2724, -2), (key2801, -1), (key2807, -1), (key2851, -1), (key2858, -1), (key2918, -1), (key2919, -1), (key2778, 1), (key2784, 1), (key2851, 1), (key2868, 1), (key2918, 1), (key2922, 1), (key3011, 2), (key3021, 2), (key3022, 2), (key3007, -2), (key3021, -2), (key3025, -2)]

theorem rawRowCheck15681 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form14 = rawRow15681 := by decide +kernel

def row15681 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1), (key3007, -2), (key3011, 2), (key3022, 2), (key3025, -2)]

theorem rowCheck15681 : row15681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15681 := by decide +kernel

theorem rowEval15681 (x : Key → ℝ) : Integer.Sparse.eval row15681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 0, 2] GramFunctions.Block4.form14) x := by
  rw [rowCheck15681, Integer.Sparse.eval_collectBalanced, rawRowCheck15681]

def rawRow15682 : Integer.Sparse Key := [(key2614, -1), (key2608, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2657, -1), (key2614, 2), (key2638, 2), (key2630, 2), (key2669, 1), (key2663, 1), (key2724, 1), (key2698, 1), (key2757, 1), (key2752, 1), (key2669, -2), (key2724, -2), (key2704, -2), (key2807, -1), (key2801, -1), (key2858, -1), (key2851, -1), (key2919, -1), (key2918, -1), (key2784, 1), (key2778, 1), (key2868, 1), (key2851, 1), (key2922, 1), (key2918, 1), (key3011, 2), (key3022, 2), (key3021, 2), (key3007, -2), (key3025, -2), (key3021, -2)]

theorem rawRowCheck15682 : GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form14 = rawRow15682 := by decide +kernel

def row15682 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1), (key3007, -2), (key3011, 2), (key3022, 2), (key3025, -2)]

theorem rowCheck15682 : row15682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15682 := by decide +kernel

theorem rowEval15682 (x : Key → ℝ) : Integer.Sparse.eval row15682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, -1, 2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck15682, Integer.Sparse.eval_collectBalanced, rawRowCheck15682]

def rawRow15683 : Integer.Sparse Key := [(key2624, -1), (key2638, -1), (key2608, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2630, 2), (key2614, 2), (key2638, 2), (key2698, 1), (key2752, 1), (key2663, 1), (key2757, 1), (key2669, 1), (key2724, 1), (key2704, -2), (key2669, -2), (key2724, -2), (key2851, -1), (key2918, -1), (key2801, -1), (key2919, -1), (key2807, -1), (key2858, -1), (key2851, 1), (key2918, 1), (key2778, 1), (key2922, 1), (key2784, 1), (key2868, 1), (key3021, 2), (key3011, 2), (key3022, 2), (key3021, -2), (key3007, -2), (key3025, -2)]

theorem rawRowCheck15683 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form14 = rawRow15683 := by decide +kernel

def row15683 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1), (key3007, -2), (key3011, 2), (key3022, 2), (key3025, -2)]

theorem rowCheck15683 : row15683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15683 := by decide +kernel

theorem rowEval15683 (x : Key → ℝ) : Integer.Sparse.eval row15683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, -1, 2] GramFunctions.Block4.form14) x := by
  rw [rowCheck15683, Integer.Sparse.eval_collectBalanced, rawRowCheck15683]

def rawRow15684 : Integer.Sparse Key := [(key2638, -1), (key2624, -1), (key2659, -1), (key2608, -1), (key2638, -1), (key2614, -1), (key2630, 2), (key2638, 2), (key2614, 2), (key2752, 1), (key2698, 1), (key2757, 1), (key2663, 1), (key2724, 1), (key2669, 1), (key2704, -2), (key2724, -2), (key2669, -2), (key2918, -1), (key2851, -1), (key2919, -1), (key2801, -1), (key2858, -1), (key2807, -1), (key2918, 1), (key2851, 1), (key2922, 1), (key2778, 1), (key2868, 1), (key2784, 1), (key3021, 2), (key3022, 2), (key3011, 2), (key3021, -2), (key3025, -2), (key3007, -2)]

theorem rawRowCheck15684 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form14 = rawRow15684 := by decide +kernel

def row15684 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1), (key3007, -2), (key3011, 2), (key3022, 2), (key3025, -2)]

theorem rowCheck15684 : row15684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15684 := by decide +kernel

theorem rowEval15684 (x : Key → ℝ) : Integer.Sparse.eval row15684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 0, 2, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck15684, Integer.Sparse.eval_collectBalanced, rawRowCheck15684]

def rawRow15685 : Integer.Sparse Key := [(key2657, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2608, -1), (key2624, -1), (key2638, 2), (key2614, 2), (key2630, 2), (key2724, 1), (key2757, 1), (key2669, 1), (key2752, 1), (key2663, 1), (key2698, 1), (key2724, -2), (key2669, -2), (key2704, -2), (key2858, -1), (key2919, -1), (key2807, -1), (key2918, -1), (key2801, -1), (key2851, -1), (key2868, 1), (key2922, 1), (key2784, 1), (key2918, 1), (key2778, 1), (key2851, 1), (key3022, 2), (key3011, 2), (key3021, 2), (key3025, -2), (key3007, -2), (key3021, -2)]

theorem rawRowCheck15685 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form14 = rawRow15685 := by decide +kernel

def row15685 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1), (key3007, -2), (key3011, 2), (key3022, 2), (key3025, -2)]

theorem rowCheck15685 : row15685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15685 := by decide +kernel

theorem rowEval15685 (x : Key → ℝ) : Integer.Sparse.eval row15685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck15685, Integer.Sparse.eval_collectBalanced, rawRowCheck15685]

def rawRow15686 : Integer.Sparse Key := [(key2659, -1), (key2657, -1), (key2638, -1), (key2614, -1), (key2624, -1), (key2608, -1), (key2638, 2), (key2630, 2), (key2614, 2), (key2757, 1), (key2724, 1), (key2752, 1), (key2669, 1), (key2698, 1), (key2663, 1), (key2724, -2), (key2704, -2), (key2669, -2), (key2919, -1), (key2858, -1), (key2918, -1), (key2807, -1), (key2851, -1), (key2801, -1), (key2922, 1), (key2868, 1), (key2918, 1), (key2784, 1), (key2851, 1), (key2778, 1), (key3022, 2), (key3021, 2), (key3011, 2), (key3025, -2), (key3021, -2), (key3007, -2)]

theorem rawRowCheck15686 : GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form14 = rawRow15686 := by decide +kernel

def row15686 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 1), (key2704, -2), (key2724, -1), (key2752, 1), (key2757, 1), (key2778, 1), (key2784, 1), (key2801, -1), (key2807, -1), (key2858, -1), (key2868, 1), (key2919, -1), (key2922, 1), (key3007, -2), (key3011, 2), (key3022, 2), (key3025, -2)]

theorem rowCheck15686 : row15686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15686 := by decide +kernel

theorem rowEval15686 (x : Key → ℝ) : Integer.Sparse.eval row15686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 0, 2, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck15686, Integer.Sparse.eval_collectBalanced, rawRowCheck15686]

def rawRow15687 : Integer.Sparse Key := [(key2614, -1), (key2614, -1), (key2630, -1), (key2630, -1), (key2638, -1), (key2638, -1), (key2608, 2), (key2624, 2), (key2624, 2), (key2669, 1), (key2669, 1), (key2704, 1), (key2704, 1), (key2752, 1), (key2752, 1), (key2663, -2), (key2698, -2), (key2698, -2), (key2827, -1), (key2827, -1), (key2868, -1), (key2868, -1), (key2922, -1), (key2922, -1), (key2792, 1), (key2792, 1), (key2858, 1), (key2858, 1), (key2919, 1), (key2919, 1), (key3016, 2), (key3025, 2), (key3025, 2), (key3009, -2), (key3022, -2), (key3022, -2)]

theorem rawRowCheck15687 : GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form14 = rawRow15687 := by decide +kernel

def row15687 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, 4), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2752, 2), (key2792, 2), (key2827, -2), (key2858, 2), (key2868, -2), (key2919, 2), (key2922, -2), (key3009, -2), (key3016, 2), (key3022, -4), (key3025, 4)]

theorem rowCheck15687 : row15687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15687 := by decide +kernel

theorem rowEval15687 (x : Key → ℝ) : Integer.Sparse.eval row15687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, -1, 0, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck15687, Integer.Sparse.eval_collectBalanced, rawRowCheck15687]

def rawRow15688 : Integer.Sparse Key := [(key2630, -1), (key2638, -1), (key2614, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2624, 2), (key2608, 2), (key2624, 2), (key2704, 1), (key2752, 1), (key2669, 1), (key2752, 1), (key2669, 1), (key2704, 1), (key2698, -2), (key2663, -2), (key2698, -2), (key2868, -1), (key2922, -1), (key2827, -1), (key2922, -1), (key2827, -1), (key2868, -1), (key2858, 1), (key2919, 1), (key2792, 1), (key2919, 1), (key2792, 1), (key2858, 1), (key3025, 2), (key3016, 2), (key3025, 2), (key3022, -2), (key3009, -2), (key3022, -2)]

theorem rawRowCheck15688 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form14 = rawRow15688 := by decide +kernel

def row15688 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, 4), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2752, 2), (key2792, 2), (key2827, -2), (key2858, 2), (key2868, -2), (key2919, 2), (key2922, -2), (key3009, -2), (key3016, 2), (key3022, -4), (key3025, 4)]

theorem rowCheck15688 : row15688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15688 := by decide +kernel

theorem rowEval15688 (x : Key → ℝ) : Integer.Sparse.eval row15688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck15688, Integer.Sparse.eval_collectBalanced, rawRowCheck15688]

def rawRow15689 : Integer.Sparse Key := [(key2638, -1), (key2630, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2614, -1), (key2624, 2), (key2624, 2), (key2608, 2), (key2752, 1), (key2704, 1), (key2752, 1), (key2669, 1), (key2704, 1), (key2669, 1), (key2698, -2), (key2698, -2), (key2663, -2), (key2922, -1), (key2868, -1), (key2922, -1), (key2827, -1), (key2868, -1), (key2827, -1), (key2919, 1), (key2858, 1), (key2919, 1), (key2792, 1), (key2858, 1), (key2792, 1), (key3025, 2), (key3025, 2), (key3016, 2), (key3022, -2), (key3022, -2), (key3009, -2)]

theorem rawRowCheck15689 : GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form14 = rawRow15689 := by decide +kernel

def row15689 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, 4), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, 2), (key2698, -4), (key2704, 2), (key2752, 2), (key2792, 2), (key2827, -2), (key2858, 2), (key2868, -2), (key2919, 2), (key2922, -2), (key3009, -2), (key3016, 2), (key3022, -4), (key3025, 4)]

theorem rowCheck15689 : row15689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15689 := by decide +kernel

theorem rowEval15689 (x : Key → ℝ) : Integer.Sparse.eval row15689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, 2, 0, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck15689, Integer.Sparse.eval_collectBalanced, rawRowCheck15689]

def rawRow15690 : Integer.Sparse Key := [(key2663, -1), (key2669, -1), (key2698, -1), (key2752, -1), (key2724, -1), (key2757, -1), (key2669, 2), (key2704, 2), (key2752, 2), (key2608, 1), (key2614, 1), (key2801, 1), (key2827, 1), (key3011, 1), (key3016, 1), (key2614, -2), (key2807, -2), (key2827, -2), (key2698, -1), (key2704, -1), (key2851, -1), (key2858, -1), (key3021, -1), (key3022, -1), (key2624, 1), (key2630, 1), (key2851, 1), (key2868, 1), (key3021, 1), (key3025, 1), (key2752, 2), (key2918, 2), (key2919, 2), (key2657, -2), (key2918, -2), (key2922, -2)]

theorem rawRowCheck15690 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form14 = rawRow15690 := by decide +kernel

def row15690 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2657, -2), (key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, -1), (key2752, 3), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -1), (key2868, 1), (key2919, 2), (key2922, -2), (key3011, 1), (key3016, 1), (key3022, -1), (key3025, 1)]

theorem rowCheck15690 : row15690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15690 := by decide +kernel

theorem rowEval15690 (x : Key → ℝ) : Integer.Sparse.eval row15690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 0, 2] GramFunctions.Block4.form14) x := by
  rw [rowCheck15690, Integer.Sparse.eval_collectBalanced, rawRowCheck15690]

def rawRow15691 : Integer.Sparse Key := [(key2669, -1), (key2663, -1), (key2752, -1), (key2698, -1), (key2757, -1), (key2724, -1), (key2669, 2), (key2752, 2), (key2704, 2), (key2614, 1), (key2608, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key3011, 1), (key2614, -2), (key2827, -2), (key2807, -2), (key2704, -1), (key2698, -1), (key2858, -1), (key2851, -1), (key3022, -1), (key3021, -1), (key2630, 1), (key2624, 1), (key2868, 1), (key2851, 1), (key3025, 1), (key3021, 1), (key2752, 2), (key2919, 2), (key2918, 2), (key2657, -2), (key2922, -2), (key2918, -2)]

theorem rawRowCheck15691 : GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form14 = rawRow15691 := by decide +kernel

def row15691 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2657, -2), (key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, -1), (key2752, 3), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -1), (key2868, 1), (key2919, 2), (key2922, -2), (key3011, 1), (key3016, 1), (key3022, -1), (key3025, 1)]

theorem rowCheck15691 : row15691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15691 := by decide +kernel

theorem rowEval15691 (x : Key → ℝ) : Integer.Sparse.eval row15691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck15691, Integer.Sparse.eval_collectBalanced, rawRowCheck15691]

def rawRow15692 : Integer.Sparse Key := [(key2698, -1), (key2724, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2704, 2), (key2669, 2), (key2752, 2), (key2801, 1), (key2827, 1), (key2608, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2807, -2), (key2614, -2), (key2827, -2), (key2851, -1), (key3021, -1), (key2698, -1), (key3022, -1), (key2704, -1), (key2858, -1), (key2851, 1), (key3021, 1), (key2624, 1), (key3025, 1), (key2630, 1), (key2868, 1), (key2918, 2), (key2752, 2), (key2919, 2), (key2918, -2), (key2657, -2), (key2922, -2)]

theorem rawRowCheck15692 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form14 = rawRow15692 := by decide +kernel

def row15692 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2657, -2), (key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, -1), (key2752, 3), (key2757, -1), (key2801, 1), (key2807, -2), (key2858, -1), (key2868, 1), (key2919, 2), (key2922, -2), (key3016, 1), (key3022, -1), (key3025, 1)]

theorem rowCheck15692 : row15692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15692 := by decide +kernel

theorem rowEval15692 (x : Key → ℝ) : Integer.Sparse.eval row15692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, -2, 2] GramFunctions.Block4.form14) x := by
  rw [rowCheck15692, Integer.Sparse.eval_collectBalanced, rawRowCheck15692]

def rawRow15693 : Integer.Sparse Key := [(key2724, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2752, -1), (key2669, -1), (key2704, 2), (key2752, 2), (key2669, 2), (key2827, 1), (key2801, 1), (key3016, 1), (key2608, 1), (key2827, 1), (key2614, 1), (key2807, -2), (key2827, -2), (key2614, -2), (key3021, -1), (key2851, -1), (key3022, -1), (key2698, -1), (key2858, -1), (key2704, -1), (key3021, 1), (key2851, 1), (key3025, 1), (key2624, 1), (key2868, 1), (key2630, 1), (key2918, 2), (key2919, 2), (key2752, 2), (key2918, -2), (key2922, -2), (key2657, -2)]

theorem rawRowCheck15693 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form14 = rawRow15693 := by decide +kernel

def row15693 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2657, -2), (key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, -1), (key2752, 3), (key2757, -1), (key2801, 1), (key2807, -2), (key2858, -1), (key2868, 1), (key2919, 2), (key2922, -2), (key3016, 1), (key3022, -1), (key3025, 1)]

theorem rowCheck15693 : row15693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15693 := by decide +kernel

theorem rowEval15693 (x : Key → ℝ) : Integer.Sparse.eval row15693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 0, 2, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck15693, Integer.Sparse.eval_collectBalanced, rawRowCheck15693]

def rawRow15694 : Integer.Sparse Key := [(key2752, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2663, -1), (key2698, -1), (key2752, 2), (key2669, 2), (key2704, 2), (key3011, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2608, 1), (key2801, 1), (key2827, -2), (key2614, -2), (key2807, -2), (key2858, -1), (key3022, -1), (key2704, -1), (key3021, -1), (key2698, -1), (key2851, -1), (key2868, 1), (key3025, 1), (key2630, 1), (key3021, 1), (key2624, 1), (key2851, 1), (key2919, 2), (key2752, 2), (key2918, 2), (key2922, -2), (key2657, -2), (key2918, -2)]

theorem rawRowCheck15694 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form14 = rawRow15694 := by decide +kernel

def row15694 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2657, -2), (key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, -1), (key2752, 3), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -1), (key2868, 1), (key2919, 2), (key2922, -2), (key3011, 1), (key3016, 1), (key3022, -1), (key3025, 1)]

theorem rowCheck15694 : row15694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15694 := by decide +kernel

theorem rowEval15694 (x : Key → ℝ) : Integer.Sparse.eval row15694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, -2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck15694, Integer.Sparse.eval_collectBalanced, rawRowCheck15694]

def rawRow15695 : Integer.Sparse Key := [(key2757, -1), (key2752, -1), (key2724, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key2752, 2), (key2704, 2), (key2669, 2), (key3016, 1), (key3011, 1), (key2827, 1), (key2614, 1), (key2801, 1), (key2608, 1), (key2827, -2), (key2807, -2), (key2614, -2), (key3022, -1), (key2858, -1), (key3021, -1), (key2704, -1), (key2851, -1), (key2698, -1), (key3025, 1), (key2868, 1), (key3021, 1), (key2630, 1), (key2851, 1), (key2624, 1), (key2919, 2), (key2918, 2), (key2752, 2), (key2922, -2), (key2918, -2), (key2657, -2)]

theorem rawRowCheck15695 : GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form14 = rawRow15695 := by decide +kernel

def row15695 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2657, -2), (key2663, -1), (key2669, 1), (key2698, -2), (key2704, 1), (key2724, -1), (key2752, 3), (key2757, -1), (key2801, 1), (key2807, -2), (key2827, -1), (key2858, -1), (key2868, 1), (key2919, 2), (key2922, -2), (key3011, 1), (key3016, 1), (key3022, -1), (key3025, 1)]

theorem rowCheck15695 : row15695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15695 := by decide +kernel

theorem rowEval15695 (x : Key → ℝ) : Integer.Sparse.eval row15695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, 2, 0, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck15695, Integer.Sparse.eval_collectBalanced, rawRowCheck15695]

def rawRow15696 : Integer.Sparse Key := [(key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2724, -1), (key2724, -1), (key2663, 2), (key2698, 2), (key2698, 2), (key2614, 1), (key2614, 1), (key2807, 1), (key2807, 1), (key2827, 1), (key2827, 1), (key2608, -2), (key2801, -2), (key2801, -2), (key2724, -1), (key2724, -1), (key2868, -1), (key2868, -1), (key3025, -1), (key3025, -1), (key2638, 1), (key2638, 1), (key2858, 1), (key2858, 1), (key3022, 1), (key3022, 1), (key2757, 2), (key2922, 2), (key2922, 2), (key2659, -2), (key2919, -2), (key2919, -2)]

theorem rawRowCheck15696 : GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form14 = rawRow15696 := by decide +kernel

def row15696 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2638, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2724, -4), (key2757, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, -2), (key2919, -4), (key2922, 4), (key3022, 2), (key3025, -2)]

theorem rowCheck15696 : row15696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15696 := by decide +kernel

theorem rowEval15696 (x : Key → ℝ) : Integer.Sparse.eval row15696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, -2, 0, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck15696, Integer.Sparse.eval_collectBalanced, rawRowCheck15696]

def rawRow15697 : Integer.Sparse Key := [(key2704, -1), (key2724, -1), (key2669, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2698, 2), (key2663, 2), (key2698, 2), (key2807, 1), (key2827, 1), (key2614, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2801, -2), (key2608, -2), (key2801, -2), (key2868, -1), (key3025, -1), (key2724, -1), (key3025, -1), (key2724, -1), (key2868, -1), (key2858, 1), (key3022, 1), (key2638, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2922, 2), (key2757, 2), (key2922, 2), (key2919, -2), (key2659, -2), (key2919, -2)]

theorem rawRowCheck15697 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form14 = rawRow15697 := by decide +kernel

def row15697 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2638, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2724, -4), (key2757, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, -2), (key2919, -4), (key2922, 4), (key3022, 2), (key3025, -2)]

theorem rowCheck15697 : row15697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15697 := by decide +kernel

theorem rowEval15697 (x : Key → ℝ) : Integer.Sparse.eval row15697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, -2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck15697, Integer.Sparse.eval_collectBalanced, rawRowCheck15697]

def rawRow15698 : Integer.Sparse Key := [(key2724, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key2698, 2), (key2698, 2), (key2663, 2), (key2827, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2614, 1), (key2801, -2), (key2801, -2), (key2608, -2), (key3025, -1), (key2868, -1), (key3025, -1), (key2724, -1), (key2868, -1), (key2724, -1), (key3022, 1), (key2858, 1), (key3022, 1), (key2638, 1), (key2858, 1), (key2638, 1), (key2922, 2), (key2922, 2), (key2757, 2), (key2919, -2), (key2919, -2), (key2659, -2)]

theorem rawRowCheck15698 : GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form14 = rawRow15698 := by decide +kernel

def row15698 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2638, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2724, -4), (key2757, 2), (key2801, -4), (key2807, 2), (key2827, 2), (key2858, 2), (key2868, -2), (key2919, -4), (key2922, 4), (key3022, 2), (key3025, -2)]

theorem rowCheck15698 : row15698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15698 := by decide +kernel

theorem rowEval15698 (x : Key → ℝ) : Integer.Sparse.eval row15698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 2, 0, 0, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck15698, Integer.Sparse.eval_collectBalanced, rawRowCheck15698]

def rawRow15699 : Integer.Sparse Key := [(key2801, -1), (key2807, -1), (key2851, -1), (key2918, -1), (key2858, -1), (key2919, -1), (key2827, 2), (key2868, 2), (key2922, 2), (key2698, 1), (key2704, 1), (key2851, 1), (key3021, 1), (key2858, 1), (key3022, 1), (key2724, -2), (key2868, -2), (key3025, -2), (key2608, -1), (key2614, -1), (key2624, -1), (key2638, -1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, 1), (key2698, 1), (key2724, 1), (key2752, 1), (key2757, 1), (key2614, 2), (key2630, 2), (key2638, 2), (key2669, -2), (key2704, -2), (key2724, -2)]

theorem rawRowCheck15699 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form14 = rawRow15699 := by decide +kernel

def row15699 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -1), (key2724, -3), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, -1), (key2827, 2), (key2918, -1), (key2919, -1), (key2922, 2), (key3021, 1), (key3022, 1), (key3025, -2)]

theorem rowCheck15699 : row15699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15699 := by decide +kernel

theorem rowEval15699 (x : Key → ℝ) : Integer.Sparse.eval row15699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 0, 2] GramFunctions.Block4.form14) x := by
  rw [rowCheck15699, Integer.Sparse.eval_collectBalanced, rawRowCheck15699]

def rawRow15700 : Integer.Sparse Key := [(key2807, -1), (key2801, -1), (key2918, -1), (key2851, -1), (key2919, -1), (key2858, -1), (key2827, 2), (key2922, 2), (key2868, 2), (key2704, 1), (key2698, 1), (key3021, 1), (key2851, 1), (key3022, 1), (key2858, 1), (key2724, -2), (key3025, -2), (key2868, -2), (key2614, -1), (key2608, -1), (key2638, -1), (key2624, -1), (key2659, -1), (key2657, -1), (key2669, 1), (key2663, 1), (key2724, 1), (key2698, 1), (key2757, 1), (key2752, 1), (key2614, 2), (key2638, 2), (key2630, 2), (key2669, -2), (key2724, -2), (key2704, -2)]

theorem rawRowCheck15700 : GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form14 = rawRow15700 := by decide +kernel

def row15700 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -1), (key2724, -3), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, -1), (key2827, 2), (key2918, -1), (key2919, -1), (key2922, 2), (key3021, 1), (key3022, 1), (key3025, -2)]

theorem rowCheck15700 : row15700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15700 := by decide +kernel

theorem rowEval15700 (x : Key → ℝ) : Integer.Sparse.eval row15700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, -1, 2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck15700, Integer.Sparse.eval_collectBalanced, rawRowCheck15700]

def rawRow15701 : Integer.Sparse Key := [(key2851, -1), (key2858, -1), (key2801, -1), (key2919, -1), (key2807, -1), (key2918, -1), (key2868, 2), (key2827, 2), (key2922, 2), (key2851, 1), (key2858, 1), (key2698, 1), (key3022, 1), (key2704, 1), (key3021, 1), (key2868, -2), (key2724, -2), (key3025, -2), (key2624, -1), (key2638, -1), (key2608, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2698, 1), (key2752, 1), (key2663, 1), (key2757, 1), (key2669, 1), (key2724, 1), (key2630, 2), (key2614, 2), (key2638, 2), (key2704, -2), (key2669, -2), (key2724, -2)]

theorem rawRowCheck15701 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form14 = rawRow15701 := by decide +kernel

def row15701 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -1), (key2724, -3), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, -1), (key2827, 2), (key2918, -1), (key2919, -1), (key2922, 2), (key3021, 1), (key3022, 1), (key3025, -2)]

theorem rowCheck15701 : row15701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15701 := by decide +kernel

theorem rowEval15701 (x : Key → ℝ) : Integer.Sparse.eval row15701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, -1, 2] GramFunctions.Block4.form14) x := by
  rw [rowCheck15701, Integer.Sparse.eval_collectBalanced, rawRowCheck15701]

def rawRow15702 : Integer.Sparse Key := [(key2858, -1), (key2851, -1), (key2919, -1), (key2801, -1), (key2918, -1), (key2807, -1), (key2868, 2), (key2922, 2), (key2827, 2), (key2858, 1), (key2851, 1), (key3022, 1), (key2698, 1), (key3021, 1), (key2704, 1), (key2868, -2), (key3025, -2), (key2724, -2), (key2638, -1), (key2624, -1), (key2659, -1), (key2608, -1), (key2638, -1), (key2614, -1), (key2752, 1), (key2698, 1), (key2757, 1), (key2663, 1), (key2724, 1), (key2669, 1), (key2630, 2), (key2638, 2), (key2614, 2), (key2704, -2), (key2724, -2), (key2669, -2)]

theorem rawRowCheck15702 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form14 = rawRow15702 := by decide +kernel

def row15702 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -1), (key2724, -3), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, -1), (key2827, 2), (key2918, -1), (key2919, -1), (key2922, 2), (key3021, 1), (key3022, 1), (key3025, -2)]

theorem rowCheck15702 : row15702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15702 := by decide +kernel

theorem rowEval15702 (x : Key → ℝ) : Integer.Sparse.eval row15702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 0, 2, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck15702, Integer.Sparse.eval_collectBalanced, rawRowCheck15702]

def rawRow15703 : Integer.Sparse Key := [(key2918, -1), (key2919, -1), (key2807, -1), (key2858, -1), (key2801, -1), (key2851, -1), (key2922, 2), (key2827, 2), (key2868, 2), (key3021, 1), (key3022, 1), (key2704, 1), (key2858, 1), (key2698, 1), (key2851, 1), (key3025, -2), (key2724, -2), (key2868, -2), (key2657, -1), (key2659, -1), (key2614, -1), (key2638, -1), (key2608, -1), (key2624, -1), (key2724, 1), (key2757, 1), (key2669, 1), (key2752, 1), (key2663, 1), (key2698, 1), (key2638, 2), (key2614, 2), (key2630, 2), (key2724, -2), (key2669, -2), (key2704, -2)]

theorem rawRowCheck15703 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form14 = rawRow15703 := by decide +kernel

def row15703 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -1), (key2724, -3), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, -1), (key2827, 2), (key2918, -1), (key2919, -1), (key2922, 2), (key3021, 1), (key3022, 1), (key3025, -2)]

theorem rowCheck15703 : row15703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15703 := by decide +kernel

theorem rowEval15703 (x : Key → ℝ) : Integer.Sparse.eval row15703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck15703, Integer.Sparse.eval_collectBalanced, rawRowCheck15703]

def rawRow15704 : Integer.Sparse Key := [(key2919, -1), (key2918, -1), (key2858, -1), (key2807, -1), (key2851, -1), (key2801, -1), (key2922, 2), (key2868, 2), (key2827, 2), (key3022, 1), (key3021, 1), (key2858, 1), (key2704, 1), (key2851, 1), (key2698, 1), (key3025, -2), (key2868, -2), (key2724, -2), (key2659, -1), (key2657, -1), (key2638, -1), (key2614, -1), (key2624, -1), (key2608, -1), (key2757, 1), (key2724, 1), (key2752, 1), (key2669, 1), (key2698, 1), (key2663, 1), (key2638, 2), (key2630, 2), (key2614, 2), (key2724, -2), (key2704, -2), (key2669, -2)]

theorem rawRowCheck15704 : GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form14 = rawRow15704 := by decide +kernel

def row15704 : Integer.Sparse Key := [(key2608, -1), (key2614, 1), (key2624, -1), (key2630, 2), (key2638, 1), (key2657, -1), (key2659, -1), (key2663, 1), (key2669, -1), (key2698, 2), (key2704, -1), (key2724, -3), (key2752, 1), (key2757, 1), (key2801, -1), (key2807, -1), (key2827, 2), (key2918, -1), (key2919, -1), (key2922, 2), (key3021, 1), (key3022, 1), (key3025, -2)]

theorem rowCheck15704 : row15704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15704 := by decide +kernel

theorem rowEval15704 (x : Key → ℝ) : Integer.Sparse.eval row15704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck15704, Integer.Sparse.eval_collectBalanced, rawRowCheck15704]

def rawRow15705 : Integer.Sparse Key := [(key2778, -1), (key2784, -1), (key2851, -1), (key2918, -1), (key2868, -1), (key2922, -1), (key2792, 2), (key2858, 2), (key2919, 2), (key2624, 1), (key2630, 1), (key2851, 1), (key3021, 1), (key2868, 1), (key3025, 1), (key2638, -2), (key2858, -2), (key3022, -2), (key2663, -1), (key2669, -1), (key2698, -1), (key2752, -1), (key2724, -1), (key2757, -1), (key2608, 1), (key2614, 1), (key2801, 1), (key2827, 1), (key3011, 1), (key3016, 1), (key2669, 2), (key2784, 2), (key2792, 2), (key2614, -2), (key2807, -2), (key2827, -2)]

theorem rawRowCheck15705 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form14 = rawRow15705 := by decide +kernel

def row15705 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2663, -1), (key2669, 1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, 1), (key2792, 4), (key2801, 1), (key2807, -2), (key2827, -1), (key2918, -1), (key2919, 2), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, 1), (key3022, -2), (key3025, 1)]

theorem rowCheck15705 : row15705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15705 := by decide +kernel

theorem rowEval15705 (x : Key → ℝ) : Integer.Sparse.eval row15705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 0, 2] GramFunctions.Block4.form14) x := by
  rw [rowCheck15705, Integer.Sparse.eval_collectBalanced, rawRowCheck15705]

def rawRow15706 : Integer.Sparse Key := [(key2784, -1), (key2778, -1), (key2918, -1), (key2851, -1), (key2922, -1), (key2868, -1), (key2792, 2), (key2919, 2), (key2858, 2), (key2630, 1), (key2624, 1), (key3021, 1), (key2851, 1), (key3025, 1), (key2868, 1), (key2638, -2), (key3022, -2), (key2858, -2), (key2669, -1), (key2663, -1), (key2752, -1), (key2698, -1), (key2757, -1), (key2724, -1), (key2614, 1), (key2608, 1), (key2827, 1), (key2801, 1), (key3016, 1), (key3011, 1), (key2669, 2), (key2792, 2), (key2784, 2), (key2614, -2), (key2827, -2), (key2807, -2)]

theorem rawRowCheck15706 : GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form14 = rawRow15706 := by decide +kernel

def row15706 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2663, -1), (key2669, 1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, 1), (key2792, 4), (key2801, 1), (key2807, -2), (key2827, -1), (key2918, -1), (key2919, 2), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, 1), (key3022, -2), (key3025, 1)]

theorem rowCheck15706 : row15706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15706 := by decide +kernel

theorem rowEval15706 (x : Key → ℝ) : Integer.Sparse.eval row15706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, -2, 2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck15706, Integer.Sparse.eval_collectBalanced, rawRowCheck15706]

def rawRow15707 : Integer.Sparse Key := [(key2851, -1), (key2868, -1), (key2778, -1), (key2922, -1), (key2784, -1), (key2918, -1), (key2858, 2), (key2792, 2), (key2919, 2), (key2851, 1), (key2868, 1), (key2624, 1), (key3025, 1), (key2630, 1), (key3021, 1), (key2858, -2), (key2638, -2), (key3022, -2), (key2698, -1), (key2724, -1), (key2663, -1), (key2757, -1), (key2669, -1), (key2752, -1), (key2801, 1), (key2827, 1), (key2608, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2784, 2), (key2669, 2), (key2792, 2), (key2807, -2), (key2614, -2), (key2827, -2)]

theorem rawRowCheck15707 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form14 = rawRow15707 := by decide +kernel

def row15707 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2663, -1), (key2669, 1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, 1), (key2792, 4), (key2801, 1), (key2807, -2), (key2918, -1), (key2919, 2), (key2922, -1), (key3016, 1), (key3021, 1), (key3022, -2), (key3025, 1)]

theorem rowCheck15707 : row15707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15707 := by decide +kernel

theorem rowEval15707 (x : Key → ℝ) : Integer.Sparse.eval row15707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block4.form14) x := by
  rw [rowCheck15707, Integer.Sparse.eval_collectBalanced, rawRowCheck15707]

def rawRow15708 : Integer.Sparse Key := [(key2868, -1), (key2851, -1), (key2922, -1), (key2778, -1), (key2918, -1), (key2784, -1), (key2858, 2), (key2919, 2), (key2792, 2), (key2868, 1), (key2851, 1), (key3025, 1), (key2624, 1), (key3021, 1), (key2630, 1), (key2858, -2), (key3022, -2), (key2638, -2), (key2724, -1), (key2698, -1), (key2757, -1), (key2663, -1), (key2752, -1), (key2669, -1), (key2827, 1), (key2801, 1), (key3016, 1), (key2608, 1), (key2827, 1), (key2614, 1), (key2784, 2), (key2792, 2), (key2669, 2), (key2807, -2), (key2827, -2), (key2614, -2)]

theorem rawRowCheck15708 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form14 = rawRow15708 := by decide +kernel

def row15708 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2663, -1), (key2669, 1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, 1), (key2792, 4), (key2801, 1), (key2807, -2), (key2918, -1), (key2919, 2), (key2922, -1), (key3016, 1), (key3021, 1), (key3022, -2), (key3025, 1)]

theorem rowCheck15708 : row15708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15708 := by decide +kernel

theorem rowEval15708 (x : Key → ℝ) : Integer.Sparse.eval row15708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, 2, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck15708, Integer.Sparse.eval_collectBalanced, rawRowCheck15708]

def rawRow15709 : Integer.Sparse Key := [(key2918, -1), (key2922, -1), (key2784, -1), (key2868, -1), (key2778, -1), (key2851, -1), (key2919, 2), (key2792, 2), (key2858, 2), (key3021, 1), (key3025, 1), (key2630, 1), (key2868, 1), (key2624, 1), (key2851, 1), (key3022, -2), (key2638, -2), (key2858, -2), (key2752, -1), (key2757, -1), (key2669, -1), (key2724, -1), (key2663, -1), (key2698, -1), (key3011, 1), (key3016, 1), (key2614, 1), (key2827, 1), (key2608, 1), (key2801, 1), (key2792, 2), (key2669, 2), (key2784, 2), (key2827, -2), (key2614, -2), (key2807, -2)]

theorem rawRowCheck15709 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form14 = rawRow15709 := by decide +kernel

def row15709 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2663, -1), (key2669, 1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, 1), (key2792, 4), (key2801, 1), (key2807, -2), (key2827, -1), (key2918, -1), (key2919, 2), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, 1), (key3022, -2), (key3025, 1)]

theorem rowCheck15709 : row15709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15709 := by decide +kernel

theorem rowEval15709 (x : Key → ℝ) : Integer.Sparse.eval row15709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, -2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck15709, Integer.Sparse.eval_collectBalanced, rawRowCheck15709]

def rawRow15710 : Integer.Sparse Key := [(key2922, -1), (key2918, -1), (key2868, -1), (key2784, -1), (key2851, -1), (key2778, -1), (key2919, 2), (key2858, 2), (key2792, 2), (key3025, 1), (key3021, 1), (key2868, 1), (key2630, 1), (key2851, 1), (key2624, 1), (key3022, -2), (key2858, -2), (key2638, -2), (key2757, -1), (key2752, -1), (key2724, -1), (key2669, -1), (key2698, -1), (key2663, -1), (key3016, 1), (key3011, 1), (key2827, 1), (key2614, 1), (key2801, 1), (key2608, 1), (key2792, 2), (key2784, 2), (key2669, 2), (key2827, -2), (key2807, -2), (key2614, -2)]

theorem rawRowCheck15710 : GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form14 = rawRow15710 := by decide +kernel

def row15710 : Integer.Sparse Key := [(key2608, 1), (key2614, -1), (key2624, 1), (key2630, 1), (key2638, -2), (key2663, -1), (key2669, 1), (key2698, -1), (key2724, -1), (key2752, -1), (key2757, -1), (key2778, -1), (key2784, 1), (key2792, 4), (key2801, 1), (key2807, -2), (key2827, -1), (key2918, -1), (key2919, 2), (key2922, -1), (key3011, 1), (key3016, 1), (key3021, 1), (key3022, -2), (key3025, 1)]

theorem rowCheck15710 : row15710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15710 := by decide +kernel

theorem rowEval15710 (x : Key → ℝ) : Integer.Sparse.eval row15710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 2, 0, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck15710, Integer.Sparse.eval_collectBalanced, rawRowCheck15710]

def rawRow15711 : Integer.Sparse Key := [(key3011, -1), (key3011, -1), (key3021, -1), (key3021, -1), (key3022, -1), (key3022, -1), (key3016, 2), (key3025, 2), (key3025, 2), (key2752, 1), (key2752, 1), (key2918, 1), (key2918, 1), (key2919, 1), (key2919, 1), (key2757, -2), (key2922, -2), (key2922, -2), (key2614, -1), (key2614, -1), (key2630, -1), (key2630, -1), (key2638, -1), (key2638, -1), (key2669, 1), (key2669, 1), (key2784, 1), (key2784, 1), (key2792, 1), (key2792, 1), (key2608, 2), (key2624, 2), (key2624, 2), (key2663, -2), (key2698, -2), (key2698, -2)]

theorem rawRowCheck15711 : GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form14 = rawRow15711 := by decide +kernel

def row15711 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, 4), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, 2), (key2698, -4), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, 2), (key2918, 2), (key2919, 2), (key2922, -4), (key3011, -2), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, 4)]

theorem rowCheck15711 : row15711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15711 := by decide +kernel

theorem rowEval15711 (x : Key → ℝ) : Integer.Sparse.eval row15711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, -1, 0, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck15711, Integer.Sparse.eval_collectBalanced, rawRowCheck15711]

def rawRow15712 : Integer.Sparse Key := [(key3021, -1), (key3022, -1), (key3011, -1), (key3022, -1), (key3011, -1), (key3021, -1), (key3025, 2), (key3016, 2), (key3025, 2), (key2918, 1), (key2919, 1), (key2752, 1), (key2919, 1), (key2752, 1), (key2918, 1), (key2922, -2), (key2757, -2), (key2922, -2), (key2630, -1), (key2638, -1), (key2614, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2784, 1), (key2792, 1), (key2669, 1), (key2792, 1), (key2669, 1), (key2784, 1), (key2624, 2), (key2608, 2), (key2624, 2), (key2698, -2), (key2663, -2), (key2698, -2)]

theorem rawRowCheck15712 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form14 = rawRow15712 := by decide +kernel

def row15712 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, 4), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, 2), (key2698, -4), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, 2), (key2918, 2), (key2919, 2), (key2922, -4), (key3011, -2), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, 4)]

theorem rowCheck15712 : row15712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15712 := by decide +kernel

theorem rowEval15712 (x : Key → ℝ) : Integer.Sparse.eval row15712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, -1, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck15712, Integer.Sparse.eval_collectBalanced, rawRowCheck15712]

def rawRow15713 : Integer.Sparse Key := [(key3022, -1), (key3021, -1), (key3022, -1), (key3011, -1), (key3021, -1), (key3011, -1), (key3025, 2), (key3025, 2), (key3016, 2), (key2919, 1), (key2918, 1), (key2919, 1), (key2752, 1), (key2918, 1), (key2752, 1), (key2922, -2), (key2922, -2), (key2757, -2), (key2638, -1), (key2630, -1), (key2638, -1), (key2614, -1), (key2630, -1), (key2614, -1), (key2792, 1), (key2784, 1), (key2792, 1), (key2669, 1), (key2784, 1), (key2669, 1), (key2624, 2), (key2624, 2), (key2608, 2), (key2698, -2), (key2698, -2), (key2663, -2)]

theorem rawRowCheck15713 : GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form14 = rawRow15713 := by decide +kernel

def row15713 : Integer.Sparse Key := [(key2608, 2), (key2614, -2), (key2624, 4), (key2630, -2), (key2638, -2), (key2663, -2), (key2669, 2), (key2698, -4), (key2752, 2), (key2757, -2), (key2784, 2), (key2792, 2), (key2918, 2), (key2919, 2), (key2922, -4), (key3011, -2), (key3016, 2), (key3021, -2), (key3022, -2), (key3025, 4)]

theorem rowCheck15713 : row15713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15713 := by decide +kernel

theorem rowEval15713 (x : Key → ℝ) : Integer.Sparse.eval row15713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -2, 0, 0, -1] GramFunctions.Block4.form14) x := by
  rw [rowCheck15713, Integer.Sparse.eval_collectBalanced, rawRowCheck15713]

def rawRow15714 : Integer.Sparse Key := [(key3007, -1), (key3007, -1), (key3021, -1), (key3021, -1), (key3025, -1), (key3025, -1), (key3009, 2), (key3022, 2), (key3022, 2), (key2657, 1), (key2657, 1), (key2918, 1), (key2918, 1), (key2922, 1), (key2922, 1), (key2659, -2), (key2919, -2), (key2919, -2), (key2669, -1), (key2669, -1), (key2704, -1), (key2704, -1), (key2724, -1), (key2724, -1), (key2614, 1), (key2614, 1), (key2807, 1), (key2807, 1), (key2827, 1), (key2827, 1), (key2663, 2), (key2698, 2), (key2698, 2), (key2608, -2), (key2801, -2), (key2801, -2)]

theorem rawRowCheck15714 : GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form14 = rawRow15714 := by decide +kernel

def row15714 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2724, -2), (key2801, -4), (key2807, 2), (key2827, 2), (key2918, 2), (key2919, -4), (key2922, 2), (key3007, -2), (key3009, 2), (key3021, -2), (key3022, 4), (key3025, -2)]

theorem rowCheck15714 : row15714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15714 := by decide +kernel

theorem rowEval15714 (x : Key → ℝ) : Integer.Sparse.eval row15714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, -2, 0, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck15714, Integer.Sparse.eval_collectBalanced, rawRowCheck15714]

def rawRow15715 : Integer.Sparse Key := [(key3021, -1), (key3025, -1), (key3007, -1), (key3025, -1), (key3007, -1), (key3021, -1), (key3022, 2), (key3009, 2), (key3022, 2), (key2918, 1), (key2922, 1), (key2657, 1), (key2922, 1), (key2657, 1), (key2918, 1), (key2919, -2), (key2659, -2), (key2919, -2), (key2704, -1), (key2724, -1), (key2669, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2807, 1), (key2827, 1), (key2614, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2698, 2), (key2663, 2), (key2698, 2), (key2801, -2), (key2608, -2), (key2801, -2)]

theorem rawRowCheck15715 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form14 = rawRow15715 := by decide +kernel

def row15715 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2724, -2), (key2801, -4), (key2807, 2), (key2827, 2), (key2918, 2), (key2919, -4), (key2922, 2), (key3007, -2), (key3009, 2), (key3021, -2), (key3022, 4), (key3025, -2)]

theorem rowCheck15715 : row15715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15715 := by decide +kernel

theorem rowEval15715 (x : Key → ℝ) : Integer.Sparse.eval row15715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, -2, 0] GramFunctions.Block4.form14) x := by
  rw [rowCheck15715, Integer.Sparse.eval_collectBalanced, rawRowCheck15715]

def rawRow15716 : Integer.Sparse Key := [(key3025, -1), (key3021, -1), (key3025, -1), (key3007, -1), (key3021, -1), (key3007, -1), (key3022, 2), (key3022, 2), (key3009, 2), (key2922, 1), (key2918, 1), (key2922, 1), (key2657, 1), (key2918, 1), (key2657, 1), (key2919, -2), (key2919, -2), (key2659, -2), (key2724, -1), (key2704, -1), (key2724, -1), (key2669, -1), (key2704, -1), (key2669, -1), (key2827, 1), (key2807, 1), (key2827, 1), (key2614, 1), (key2807, 1), (key2614, 1), (key2698, 2), (key2698, 2), (key2663, 2), (key2801, -2), (key2801, -2), (key2608, -2)]

theorem rawRowCheck15716 : GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form14 = rawRow15716 := by decide +kernel

def row15716 : Integer.Sparse Key := [(key2608, -2), (key2614, 2), (key2657, 2), (key2659, -2), (key2663, 2), (key2669, -2), (key2698, 4), (key2704, -2), (key2724, -2), (key2801, -4), (key2807, 2), (key2827, 2), (key2918, 2), (key2919, -4), (key2922, 2), (key3007, -2), (key3009, 2), (key3021, -2), (key3022, 4), (key3025, -2)]

theorem rowCheck15716 : row15716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15716 := by decide +kernel

theorem rowEval15716 (x : Key → ℝ) : Integer.Sparse.eval row15716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, -1, 0, 0, -2] GramFunctions.Block4.form14) x := by
  rw [rowCheck15716, Integer.Sparse.eval_collectBalanced, rawRowCheck15716]

def rawRow15717 : Integer.Sparse Key := [(key2406, 4), (key2480, 4), (key2543, 4), (key2406, -2), (key2409, -2), (key2472, -2), (key2538, -2), (key2482, -2), (key2543, -2), (key2437, -2), (key2440, -2), (key2503, -2), (key2554, -2), (key2522, -2), (key2563, -2), (key2440, 4), (key2506, 4), (key2554, 4)]

theorem rawRowCheck15717 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form0 = rawRow15717 := by decide +kernel

def row15717 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck15717 : row15717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15717 := by decide +kernel

theorem rowEval15717 (x : Key → ℝ) : Integer.Sparse.eval row15717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck15717, Integer.Sparse.eval_collectBalanced, rawRowCheck15717]

def rawRow15718 : Integer.Sparse Key := [(key2406, 4), (key2543, 4), (key2480, 4), (key2409, -2), (key2406, -2), (key2538, -2), (key2472, -2), (key2543, -2), (key2482, -2), (key2440, -2), (key2437, -2), (key2554, -2), (key2503, -2), (key2563, -2), (key2522, -2), (key2440, 4), (key2554, 4), (key2506, 4)]

theorem rawRowCheck15718 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form0 = rawRow15718 := by decide +kernel

def row15718 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck15718 : row15718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15718 := by decide +kernel

theorem rowEval15718 (x : Key → ℝ) : Integer.Sparse.eval row15718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15718, Integer.Sparse.eval_collectBalanced, rawRowCheck15718]

def rawRow15719 : Integer.Sparse Key := [(key2480, 4), (key2406, 4), (key2543, 4), (key2472, -2), (key2482, -2), (key2406, -2), (key2543, -2), (key2409, -2), (key2538, -2), (key2503, -2), (key2522, -2), (key2437, -2), (key2563, -2), (key2440, -2), (key2554, -2), (key2506, 4), (key2440, 4), (key2554, 4)]

theorem rawRowCheck15719 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form0 = rawRow15719 := by decide +kernel

def row15719 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck15719 : row15719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15719 := by decide +kernel

theorem rowEval15719 (x : Key → ℝ) : Integer.Sparse.eval row15719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck15719, Integer.Sparse.eval_collectBalanced, rawRowCheck15719]

def rawRow15720 : Integer.Sparse Key := [(key2480, 4), (key2543, 4), (key2406, 4), (key2482, -2), (key2472, -2), (key2543, -2), (key2406, -2), (key2538, -2), (key2409, -2), (key2522, -2), (key2503, -2), (key2563, -2), (key2437, -2), (key2554, -2), (key2440, -2), (key2506, 4), (key2554, 4), (key2440, 4)]

theorem rawRowCheck15720 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form0 = rawRow15720 := by decide +kernel

def row15720 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck15720 : row15720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15720 := by decide +kernel

theorem rowEval15720 (x : Key → ℝ) : Integer.Sparse.eval row15720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck15720, Integer.Sparse.eval_collectBalanced, rawRowCheck15720]

def rawRow15721 : Integer.Sparse Key := [(key2543, 4), (key2406, 4), (key2480, 4), (key2538, -2), (key2543, -2), (key2409, -2), (key2482, -2), (key2406, -2), (key2472, -2), (key2554, -2), (key2563, -2), (key2440, -2), (key2522, -2), (key2437, -2), (key2503, -2), (key2554, 4), (key2440, 4), (key2506, 4)]

theorem rawRowCheck15721 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form0 = rawRow15721 := by decide +kernel

def row15721 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck15721 : row15721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15721 := by decide +kernel

theorem rowEval15721 (x : Key → ℝ) : Integer.Sparse.eval row15721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15721, Integer.Sparse.eval_collectBalanced, rawRowCheck15721]

def rawRow15722 : Integer.Sparse Key := [(key2543, 4), (key2480, 4), (key2406, 4), (key2543, -2), (key2538, -2), (key2482, -2), (key2409, -2), (key2472, -2), (key2406, -2), (key2563, -2), (key2554, -2), (key2522, -2), (key2440, -2), (key2503, -2), (key2437, -2), (key2554, 4), (key2506, 4), (key2440, 4)]

theorem rawRowCheck15722 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form0 = rawRow15722 := by decide +kernel

def row15722 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck15722 : row15722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15722 := by decide +kernel

theorem rowEval15722 (x : Key → ℝ) : Integer.Sparse.eval row15722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck15722, Integer.Sparse.eval_collectBalanced, rawRowCheck15722]

def rawRow15723 : Integer.Sparse Key := [(key2409, 4), (key2482, 4), (key2482, 4), (key2406, -2), (key2406, -2), (key2472, -2), (key2472, -2), (key2480, -2), (key2480, -2), (key2440, -2), (key2440, -2), (key2506, -2), (key2506, -2), (key2522, -2), (key2522, -2), (key2437, 4), (key2503, 4), (key2503, 4)]

theorem rawRowCheck15723 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form0 = rawRow15723 := by decide +kernel

def row15723 : Integer.Sparse Key := [(key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2472, -4), (key2480, -4), (key2482, 8), (key2503, 8), (key2506, -4), (key2522, -4)]

theorem rowCheck15723 : row15723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15723 := by decide +kernel

theorem rowEval15723 (x : Key → ℝ) : Integer.Sparse.eval row15723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15723, Integer.Sparse.eval_collectBalanced, rawRowCheck15723]

def rawRow15724 : Integer.Sparse Key := [(key2482, 4), (key2409, 4), (key2482, 4), (key2472, -2), (key2480, -2), (key2406, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2506, -2), (key2522, -2), (key2440, -2), (key2522, -2), (key2440, -2), (key2506, -2), (key2503, 4), (key2437, 4), (key2503, 4)]

theorem rawRowCheck15724 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form0 = rawRow15724 := by decide +kernel

def row15724 : Integer.Sparse Key := [(key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2472, -4), (key2480, -4), (key2482, 8), (key2503, 8), (key2506, -4), (key2522, -4)]

theorem rowCheck15724 : row15724 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15724 := by decide +kernel

theorem rowEval15724 (x : Key → ℝ) : Integer.Sparse.eval row15724 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15724, Integer.Sparse.eval_collectBalanced, rawRowCheck15724]

def rawRow15725 : Integer.Sparse Key := [(key2482, 4), (key2482, 4), (key2409, 4), (key2480, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2406, -2), (key2522, -2), (key2506, -2), (key2522, -2), (key2440, -2), (key2506, -2), (key2440, -2), (key2503, 4), (key2503, 4), (key2437, 4)]

theorem rawRowCheck15725 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form0 = rawRow15725 := by decide +kernel

def row15725 : Integer.Sparse Key := [(key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2472, -4), (key2480, -4), (key2482, 8), (key2503, 8), (key2506, -4), (key2522, -4)]

theorem rowCheck15725 : row15725 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15725 := by decide +kernel

theorem rowEval15725 (x : Key → ℝ) : Integer.Sparse.eval row15725 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck15725, Integer.Sparse.eval_collectBalanced, rawRowCheck15725]

def rawRow15726 : Integer.Sparse Key := [(key2406, 4), (key2480, 4), (key2543, 4), (key2437, -2), (key2440, -2), (key2503, -2), (key2554, -2), (key2522, -2), (key2563, -2), (key2406, -2), (key2409, -2), (key2472, -2), (key2538, -2), (key2482, -2), (key2543, -2), (key2440, 4), (key2506, 4), (key2554, 4)]

theorem rawRowCheck15726 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form0 = rawRow15726 := by decide +kernel

def row15726 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck15726 : row15726 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15726 := by decide +kernel

theorem rowEval15726 (x : Key → ℝ) : Integer.Sparse.eval row15726 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck15726, Integer.Sparse.eval_collectBalanced, rawRowCheck15726]

def rawRow15727 : Integer.Sparse Key := [(key2406, 4), (key2543, 4), (key2480, 4), (key2440, -2), (key2437, -2), (key2554, -2), (key2503, -2), (key2563, -2), (key2522, -2), (key2409, -2), (key2406, -2), (key2538, -2), (key2472, -2), (key2543, -2), (key2482, -2), (key2440, 4), (key2554, 4), (key2506, 4)]

theorem rawRowCheck15727 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form0 = rawRow15727 := by decide +kernel

def row15727 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck15727 : row15727 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15727 := by decide +kernel

theorem rowEval15727 (x : Key → ℝ) : Integer.Sparse.eval row15727 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15727, Integer.Sparse.eval_collectBalanced, rawRowCheck15727]

def rawRow15728 : Integer.Sparse Key := [(key2480, 4), (key2406, 4), (key2543, 4), (key2503, -2), (key2522, -2), (key2437, -2), (key2563, -2), (key2440, -2), (key2554, -2), (key2472, -2), (key2482, -2), (key2406, -2), (key2543, -2), (key2409, -2), (key2538, -2), (key2506, 4), (key2440, 4), (key2554, 4)]

theorem rawRowCheck15728 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form0 = rawRow15728 := by decide +kernel

def row15728 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck15728 : row15728 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15728 := by decide +kernel

theorem rowEval15728 (x : Key → ℝ) : Integer.Sparse.eval row15728 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block4.form0) x := by
  rw [rowCheck15728, Integer.Sparse.eval_collectBalanced, rawRowCheck15728]

def rawRow15729 : Integer.Sparse Key := [(key2480, 4), (key2543, 4), (key2406, 4), (key2522, -2), (key2503, -2), (key2563, -2), (key2437, -2), (key2554, -2), (key2440, -2), (key2482, -2), (key2472, -2), (key2543, -2), (key2406, -2), (key2538, -2), (key2409, -2), (key2506, 4), (key2554, 4), (key2440, 4)]

theorem rawRowCheck15729 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form0 = rawRow15729 := by decide +kernel

def row15729 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck15729 : row15729 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15729 := by decide +kernel

theorem rowEval15729 (x : Key → ℝ) : Integer.Sparse.eval row15729 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck15729, Integer.Sparse.eval_collectBalanced, rawRowCheck15729]

def rawRow15730 : Integer.Sparse Key := [(key2543, 4), (key2406, 4), (key2480, 4), (key2554, -2), (key2563, -2), (key2440, -2), (key2522, -2), (key2437, -2), (key2503, -2), (key2538, -2), (key2543, -2), (key2409, -2), (key2482, -2), (key2406, -2), (key2472, -2), (key2554, 4), (key2440, 4), (key2506, 4)]

theorem rawRowCheck15730 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form0 = rawRow15730 := by decide +kernel

def row15730 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck15730 : row15730 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15730 := by decide +kernel

theorem rowEval15730 (x : Key → ℝ) : Integer.Sparse.eval row15730 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15730, Integer.Sparse.eval_collectBalanced, rawRowCheck15730]

def rawRow15731 : Integer.Sparse Key := [(key2543, 4), (key2480, 4), (key2406, 4), (key2563, -2), (key2554, -2), (key2522, -2), (key2440, -2), (key2503, -2), (key2437, -2), (key2543, -2), (key2538, -2), (key2482, -2), (key2409, -2), (key2472, -2), (key2406, -2), (key2554, 4), (key2506, 4), (key2440, 4)]

theorem rawRowCheck15731 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form0 = rawRow15731 := by decide +kernel

def row15731 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, 2), (key2563, -2)]

theorem rowCheck15731 : row15731 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15731 := by decide +kernel

theorem rowEval15731 (x : Key → ℝ) : Integer.Sparse.eval row15731 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck15731, Integer.Sparse.eval_collectBalanced, rawRowCheck15731]

def rawRow15732 : Integer.Sparse Key := [(key2409, 4), (key2482, 4), (key2482, 4), (key2440, -2), (key2440, -2), (key2506, -2), (key2506, -2), (key2522, -2), (key2522, -2), (key2406, -2), (key2406, -2), (key2472, -2), (key2472, -2), (key2480, -2), (key2480, -2), (key2437, 4), (key2503, 4), (key2503, 4)]

theorem rawRowCheck15732 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form0 = rawRow15732 := by decide +kernel

def row15732 : Integer.Sparse Key := [(key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2472, -4), (key2480, -4), (key2482, 8), (key2503, 8), (key2506, -4), (key2522, -4)]

theorem rowCheck15732 : row15732 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15732 := by decide +kernel

theorem rowEval15732 (x : Key → ℝ) : Integer.Sparse.eval row15732 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15732, Integer.Sparse.eval_collectBalanced, rawRowCheck15732]

def rawRow15733 : Integer.Sparse Key := [(key2482, 4), (key2409, 4), (key2482, 4), (key2506, -2), (key2522, -2), (key2440, -2), (key2522, -2), (key2440, -2), (key2506, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2503, 4), (key2437, 4), (key2503, 4)]

theorem rawRowCheck15733 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form0 = rawRow15733 := by decide +kernel

def row15733 : Integer.Sparse Key := [(key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2472, -4), (key2480, -4), (key2482, 8), (key2503, 8), (key2506, -4), (key2522, -4)]

theorem rowCheck15733 : row15733 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15733 := by decide +kernel

theorem rowEval15733 (x : Key → ℝ) : Integer.Sparse.eval row15733 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block4.form0) x := by
  rw [rowCheck15733, Integer.Sparse.eval_collectBalanced, rawRowCheck15733]

def rawRow15734 : Integer.Sparse Key := [(key2482, 4), (key2482, 4), (key2409, 4), (key2522, -2), (key2506, -2), (key2522, -2), (key2440, -2), (key2506, -2), (key2440, -2), (key2480, -2), (key2472, -2), (key2480, -2), (key2406, -2), (key2472, -2), (key2406, -2), (key2503, 4), (key2503, 4), (key2437, 4)]

theorem rawRowCheck15734 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form0 = rawRow15734 := by decide +kernel

def row15734 : Integer.Sparse Key := [(key2406, -4), (key2409, 4), (key2437, 4), (key2440, -4), (key2472, -4), (key2480, -4), (key2482, 8), (key2503, 8), (key2506, -4), (key2522, -4)]

theorem rowCheck15734 : row15734 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15734 := by decide +kernel

theorem rowEval15734 (x : Key → ℝ) : Integer.Sparse.eval row15734 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block4.form0) x := by
  rw [rowCheck15734, Integer.Sparse.eval_collectBalanced, rawRowCheck15734]

def rawRow15735 : Integer.Sparse Key := [(key994, -2), (key999, -2), (key1013, -2), (key999, 6), (key1107, -2), (key1112, -2), (key1121, -2), (key1029, 2), (key1034, 2), (key1107, 2), (key1191, 2), (key1121, 2), (key1197, 2), (key1034, -2), (key1112, -2), (key1191, -2), (key1148, 6), (key1069, -2), (key1148, -2), (key1210, -2)]

theorem rawRowCheck15735 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form1 = rawRow15735 := by decide +kernel

def row15735 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

theorem rowCheck15735 : row15735 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15735 := by decide +kernel

theorem rowEval15735 (x : Key → ℝ) : Integer.Sparse.eval row15735 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 0, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck15735, Integer.Sparse.eval_collectBalanced, rawRowCheck15735]

def rawRow15736 : Integer.Sparse Key := [(key999, -2), (key994, -2), (key1013, -2), (key999, 6), (key1112, -2), (key1107, -2), (key1121, -2), (key1034, 2), (key1029, 2), (key1191, 2), (key1107, 2), (key1197, 2), (key1121, 2), (key1034, -2), (key1191, -2), (key1112, -2), (key1148, 6), (key1069, -2), (key1210, -2), (key1148, -2)]

theorem rawRowCheck15736 : GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form1 = rawRow15736 := by decide +kernel

def row15736 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

theorem rowCheck15736 : row15736 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15736 := by decide +kernel

theorem rowEval15736 (x : Key → ℝ) : Integer.Sparse.eval row15736 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, -1, 1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15736, Integer.Sparse.eval_collectBalanced, rawRowCheck15736]

def rawRow15737 : Integer.Sparse Key := [(key994, -2), (key1013, -2), (key999, -2), (key999, 6), (key1107, -2), (key1121, -2), (key1112, -2), (key1107, 2), (key1121, 2), (key1029, 2), (key1197, 2), (key1034, 2), (key1191, 2), (key1112, -2), (key1034, -2), (key1191, -2), (key1148, 6), (key1148, -2), (key1069, -2), (key1210, -2)]

theorem rawRowCheck15737 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form1 = rawRow15737 := by decide +kernel

def row15737 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

theorem rowCheck15737 : row15737 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15737 := by decide +kernel

theorem rowEval15737 (x : Key → ℝ) : Integer.Sparse.eval row15737 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, -1, 1] GramFunctions.Block4.form1) x := by
  rw [rowCheck15737, Integer.Sparse.eval_collectBalanced, rawRowCheck15737]

def rawRow15738 : Integer.Sparse Key := [(key1013, -2), (key994, -2), (key999, -2), (key999, 6), (key1121, -2), (key1107, -2), (key1112, -2), (key1121, 2), (key1107, 2), (key1197, 2), (key1029, 2), (key1191, 2), (key1034, 2), (key1112, -2), (key1191, -2), (key1034, -2), (key1148, 6), (key1148, -2), (key1210, -2), (key1069, -2)]

theorem rawRowCheck15738 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form1 = rawRow15738 := by decide +kernel

def row15738 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

theorem rowCheck15738 : row15738 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15738 := by decide +kernel

theorem rowEval15738 (x : Key → ℝ) : Integer.Sparse.eval row15738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 0, 1, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck15738, Integer.Sparse.eval_collectBalanced, rawRowCheck15738]

def rawRow15739 : Integer.Sparse Key := [(key999, -2), (key1013, -2), (key994, -2), (key999, 6), (key1112, -2), (key1121, -2), (key1107, -2), (key1191, 2), (key1197, 2), (key1034, 2), (key1121, 2), (key1029, 2), (key1107, 2), (key1191, -2), (key1034, -2), (key1112, -2), (key1148, 6), (key1210, -2), (key1069, -2), (key1148, -2)]

theorem rawRowCheck15739 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form1 = rawRow15739 := by decide +kernel

def row15739 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

theorem rowCheck15739 : row15739 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15739 := by decide +kernel

theorem rowEval15739 (x : Key → ℝ) : Integer.Sparse.eval row15739 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15739, Integer.Sparse.eval_collectBalanced, rawRowCheck15739]

def rawRow15740 : Integer.Sparse Key := [(key1013, -2), (key999, -2), (key994, -2), (key999, 6), (key1121, -2), (key1112, -2), (key1107, -2), (key1197, 2), (key1191, 2), (key1121, 2), (key1034, 2), (key1107, 2), (key1029, 2), (key1191, -2), (key1112, -2), (key1034, -2), (key1148, 6), (key1210, -2), (key1148, -2), (key1069, -2)]

theorem rawRowCheck15740 : GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form1 = rawRow15740 := by decide +kernel

def row15740 : Integer.Sparse Key := [(key994, -2), (key999, 4), (key1013, -2), (key1029, 2), (key1069, -2), (key1112, -4), (key1148, 4), (key1197, 2), (key1210, -2)]

theorem rowCheck15740 : row15740 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15740 := by decide +kernel

theorem rowEval15740 (x : Key → ℝ) : Integer.Sparse.eval row15740 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 0, 1, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck15740, Integer.Sparse.eval_collectBalanced, rawRowCheck15740]

def rawRow15741 : Integer.Sparse Key := [(key999, -2), (key999, -2), (key1013, -2), (key994, 6), (key1191, -2), (key1191, -2), (key1197, -2), (key1034, 2), (key1034, 2), (key1112, 2), (key1112, 2), (key1121, 2), (key1121, 2), (key1029, -2), (key1107, -2), (key1107, -2), (key1210, 6), (key1069, -2), (key1148, -2), (key1148, -2)]

theorem rawRowCheck15741 : GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form1 = rawRow15741 := by decide +kernel

def row15741 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

theorem rowCheck15741 : row15741 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15741 := by decide +kernel

theorem rowEval15741 (x : Key → ℝ) : Integer.Sparse.eval row15741 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, -1, 0, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15741, Integer.Sparse.eval_collectBalanced, rawRowCheck15741]

def rawRow15742 : Integer.Sparse Key := [(key999, -2), (key1013, -2), (key999, -2), (key994, 6), (key1191, -2), (key1197, -2), (key1191, -2), (key1112, 2), (key1121, 2), (key1034, 2), (key1121, 2), (key1034, 2), (key1112, 2), (key1107, -2), (key1029, -2), (key1107, -2), (key1210, 6), (key1148, -2), (key1069, -2), (key1148, -2)]

theorem rawRowCheck15742 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form1 = rawRow15742 := by decide +kernel

def row15742 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

theorem rowCheck15742 : row15742 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15742 := by decide +kernel

theorem rowEval15742 (x : Key → ℝ) : Integer.Sparse.eval row15742 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, -1, 0] GramFunctions.Block4.form1) x := by
  rw [rowCheck15742, Integer.Sparse.eval_collectBalanced, rawRowCheck15742]

def rawRow15743 : Integer.Sparse Key := [(key1013, -2), (key999, -2), (key999, -2), (key994, 6), (key1197, -2), (key1191, -2), (key1191, -2), (key1121, 2), (key1112, 2), (key1121, 2), (key1034, 2), (key1112, 2), (key1034, 2), (key1107, -2), (key1107, -2), (key1029, -2), (key1210, 6), (key1148, -2), (key1148, -2), (key1069, -2)]

theorem rawRowCheck15743 : GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form1 = rawRow15743 := by decide +kernel

def row15743 : Integer.Sparse Key := [(key994, 6), (key999, -4), (key1013, -2), (key1029, -2), (key1034, 4), (key1069, -2), (key1107, -4), (key1112, 4), (key1121, 4), (key1148, -4), (key1191, -4), (key1197, -2), (key1210, 6)]

theorem rowCheck15743 : row15743 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15743 := by decide +kernel

theorem rowEval15743 (x : Key → ℝ) : Integer.Sparse.eval row15743 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -2, 1, 0, 0, -1] GramFunctions.Block4.form1) x := by
  rw [rowCheck15743, Integer.Sparse.eval_collectBalanced, rawRowCheck15743]

end MUB6.Certificate.GramRows

end OAI
