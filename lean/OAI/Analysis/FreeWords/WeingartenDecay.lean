import Mathlib
import OAI.Analysis.FreeWords.PowerMetricInverse

namespace OAI

noncomputable section

namespace KKWeingarten

open scoped BigOperators

noncomputable section

theorem weingarten_decay (r : ℕ) : ∃ (C : ℝ) (D : ℕ), 0 < C ∧ 0 < D ∧
    ∀ d : ℕ, D ≤ d → ∀ π σ : Equiv.Perm (Fin r),
      ‖(permutationGram r d)⁻¹ π σ‖ ≤ C / (d : ℝ)^(r+permutationDistance π σ) := by
  classical
  let m := Fintype.card (Equiv.Perm (Fin r))
  have hm : 0 < m := Fintype.card_pos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hL : (1 : ℝ) ≤ 2*m := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  refine ⟨2*(2*(m : ℝ))^r,max r (2*m),by positivity,lt_of_lt_of_le (by omega) (le_max_right _ _),?_⟩
  intro d hd π σ
  have hrd : r ≤ d := (le_max_left _ _).trans hd
  have hLd : 2*m ≤ d := (le_max_right _ _).trans hd
  have hdpos : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hds : 2*(m : ℝ)*(d : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hdR).mpr (by exact_mod_cast hLd)
  let B := (d : ℂ)^r • (permutationGram r d)⁻¹
  have hB : distanceMatrix permutationDistance (d : ℝ)⁻¹*B=1 := by
    dsimp [B]
    rw [Matrix.mul_smul,← Matrix.smul_mul,← permutationGram_scalar_distance hdpos]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (permutationGram_det_ne_zero hrd))
  have hb := distanceMatrix_inverse_bound permutationDistance permutationDistance_self
    (fun i k hik => Nat.pos_of_ne_zero (fun he => hik ((permutationDistance_eq_zero i k).mp he)))
    permutationDistance_triangle (d : ℝ)⁻¹ (inv_pos.mpr hdR) hds B hB π σ
  change ‖(d : ℂ)^r*((permutationGram r d)⁻¹ π σ)‖ ≤
    2*(2*(m : ℝ)*(d : ℝ)⁻¹)^permutationDistance π σ at hb
  rw [norm_mul,norm_pow,Complex.norm_natCast] at hb
  have hdist : permutationDistance π σ ≤ r := by
    have hh := permutationDistance_add_classes π σ
    omega
  have he : (2*(m : ℝ)*(d : ℝ)⁻¹)^permutationDistance π σ*(d : ℝ)^permutationDistance π σ =
      (2*(m : ℝ))^permutationDistance π σ := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hb' := mul_le_mul_of_nonneg_right hb (pow_nonneg hdR.le (permutationDistance π σ))
  have hb'' : ‖(permutationGram r d)⁻¹ π σ‖*(d : ℝ)^(r+permutationDistance π σ) ≤
      2*(2*(m : ℝ))^permutationDistance π σ := by
    rw [pow_add]
    calc
      _ = ((d : ℝ)^r*‖(permutationGram r d)⁻¹ π σ‖)*(d : ℝ)^permutationDistance π σ := by ring
      _ ≤ 2 * ((2*(m : ℝ)*(d : ℝ)⁻¹)^permutationDistance π σ * (d : ℝ)^permutationDistance π σ) := by nlinarith [hb']
      _ = _ := by rw [he]
  apply (le_div_iff₀ (pow_pos hdR _)).mpr
  exact hb''.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hdist) (by norm_num))

end

end KKWeingarten
end

end OAI
