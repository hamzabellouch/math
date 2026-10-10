import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

/-! # Multiplying a first-order vector expansion by a complex exponential -/

namespace DefocusingNLS
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem complex_exp_sub_one_bound (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := by
  calc
    _ ≤ ‖Complex.exp z - 1 - z‖ + ‖z‖ := by
      have h := norm_add_le (Complex.exp z - 1 - z) z
      simpa only [sub_add_cancel] using h
    _ ≤ ‖z‖ ^ 2 + ‖z‖ := add_le_add (Complex.norm_exp_sub_one_sub_id_le hz) le_rfl
    _ ≤ _ := by nlinarith [norm_nonneg z]

theorem exponential_modulation_taylor (z : ℂ) (hz : ‖z‖ ≤ 1) (u q d : V) :
    ‖Complex.exp z • u - q - (z • q + d)‖ ≤
      ‖u - q - d‖ + ‖z‖ ^ 2 * ‖q‖ + 2 * ‖z‖ * ‖u - q‖ := by
  have he : Complex.exp z • u - q - (z • q + d) =
      (u - q - d) + (Complex.exp z - 1 - z) • q +
        (Complex.exp z - 1) • (u - q) := by
    simp only [sub_smul, one_smul, smul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖u - q - d‖ + ‖(Complex.exp z - 1 - z) • q‖ +
        ‖(Complex.exp z - 1) • (u - q)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [norm_smul]
      exact add_le_add (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (Complex.norm_exp_sub_one_sub_id_le hz) (norm_nonneg q)))
        (mul_le_mul_of_nonneg_right (complex_exp_sub_one_bound z hz) (norm_nonneg _))

end DefocusingNLS

end OAI
