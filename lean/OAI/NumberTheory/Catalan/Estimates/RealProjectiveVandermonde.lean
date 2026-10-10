import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open scoped BigOperators

namespace InternalCatalan

private theorem norm_real_add_I (z : ℝ) :
    ‖(z : ℂ) + Complex.I‖ = Real.sqrt (1 + z ^ 2) := by
  simp [Complex.norm_eq_sqrt_sq_add_sq, add_comm]

private theorem norm_real_sub_I (z : ℝ) :
    ‖(z : ℂ) - Complex.I‖ = Real.sqrt (1 + z ^ 2) := by
  simp [Complex.norm_eq_sqrt_sq_add_sq, add_comm]

theorem real_projectiveVandermonde_entry_norm {m : ℕ} (z : Fin m → ℝ)
    (i j : Fin m) :
    ‖Matrix.projVandermonde
      (fun i => (z i : ℂ) + Complex.I) (fun i => (z i : ℂ) - Complex.I) i j‖ =
      Real.sqrt (1 + z i ^ 2) ^ (m - 1) := by
  rw [Matrix.projVandermonde_apply, Complex.norm_mul, Complex.norm_pow, Complex.norm_pow,
    norm_real_add_I, norm_real_sub_I, ← pow_add]
  congr 1
  rw [Fin.val_rev]
  omega

private theorem real_projective_pair_norm (a b : ℝ) :
    ‖((b : ℂ) + Complex.I) * ((a : ℂ) - Complex.I) -
      ((a : ℂ) + Complex.I) * ((b : ℂ) - Complex.I)‖ = 2 * |b - a| := by
  have heq : ((b : ℂ) + Complex.I) * ((a : ℂ) - Complex.I) -
      ((a : ℂ) + Complex.I) * ((b : ℂ) - Complex.I) =
      (-2 * Complex.I) * ((b - a : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.norm_mul, Complex.norm_mul, Complex.norm_real]
  norm_num [Real.norm_eq_abs]

private theorem prod_two_pairs (m : ℕ) :
    (∏ i : Fin m, ∏ _j ∈ Finset.Ioi i, (2 : ℝ)) = 2 ^ (m.choose 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
    simp only [Fin.prod_Ioi_succ]
    rw [ih]
    simp only [Finset.prod_const, Finset.card_fin]
    have hc : (m + 1).choose 2 = m + m.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ m 1
    rw [hc, pow_add]

theorem real_projectiveVandermonde_det_norm {m : ℕ} (z : Fin m → ℝ) :
    ‖Matrix.det (Matrix.projVandermonde
      (fun i => (z i : ℂ) + Complex.I) (fun i => (z i : ℂ) - Complex.I))‖ =
      2 ^ (m.choose 2) *
        |∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (z j - z i)| := by
  rw [Matrix.det_projVandermonde]
  simp_rw [Complex.norm_prod, real_projective_pair_norm]
  simp only [Finset.prod_mul_distrib]
  rw [prod_two_pairs]
  simp_rw [Finset.abs_prod]

end InternalCatalan

end

end OAI
