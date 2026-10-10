import OAI.Geometry.RCD.Heat.GaussianScaleAbsorption

namespace OAI

/-! # Uniform Gaussian bounds at a fixed positive separation -/

noncomputable section
namespace RegularPointCoordinates

/-- A positive separation absorbs every inverse power of the heat scale,
uniformly over all positive scales. -/
theorem exists_separated_gaussian_bound (n : ℕ) {δ D : ℝ} (hδ : 0 < δ) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧ ∀ s d : ℝ, 0 < s → δ ≤ d →
      s⁻¹ ^ n * Real.exp (-d ^ 2 / (D * s ^ 2)) ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_gaussian_polynomial_bound n (inv_pos.mpr hD)
  refine ⟨δ⁻¹ ^ n * C, by positivity, ?_⟩
  intro s d hs hdist
  have hd : 0 ≤ d := hδ.le.trans hdist
  have hsq : δ ^ 2 ≤ d ^ 2 := (sq_le_sq₀ hδ.le hd).mpr hdist
  have hexp : Real.exp (-d ^ 2 / (D * s ^ 2)) ≤ Real.exp (-δ ^ 2 / (D * s ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have hh := div_le_div_of_nonneg_right hsq (by positivity : 0 ≤ D * s ^ 2)
    simpa only [neg_div] using neg_le_neg hh
  apply (mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ s⁻¹ ^ n)).trans
  by_cases hlarge : δ ≤ s
  · have hi0 : s⁻¹ ≤ δ⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hδ hlarge
    have hi : s⁻¹ ^ n ≤ δ⁻¹ ^ n := pow_le_pow_left₀ (by positivity) hi0 n
    have he : Real.exp (-δ ^ 2 / (D * s ^ 2)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
    calc
      _ ≤ s⁻¹ ^ n := mul_le_of_le_one_right (by positivity) he
      _ ≤ δ⁻¹ ^ n := hi
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hC
  · have hu : 1 ≤ δ / s := (le_div_iff₀ hs).mpr (by
      simpa only [one_mul] using (le_of_not_ge hlarge : s ≤ δ))
    have h := mul_le_mul_of_nonneg_left (hb (δ / s) hu) (by positivity : 0 ≤ δ⁻¹ ^ n)
    have he : -D⁻¹ * (δ / s) ^ 2 = -δ ^ 2 / (D * s ^ 2) := by field_simp
    rw [he] at h
    have hc : δ⁻¹ ^ n * (δ / s) ^ n = s⁻¹ ^ n := by
      rw [← mul_pow]
      congr 1
      field_simp
    simpa only [← mul_assoc, hc] using h

end RegularPointCoordinates

end

end OAI
