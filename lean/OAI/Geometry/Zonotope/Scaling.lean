import OAI.Geometry.Zonotope.Halfspaces

namespace OAI

noncomputable section
open Set
open scoped BigOperators

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma coordinate_pairing_smul (u x : ι → ℝ) (c : ℝ) :
    (∑ i, u i * (c • x) i) = c * ∑ i, u i * x i := by
  calc
    _ = ∑ i, c * (u i * x i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_left_comm (u i) c (x i)
    _ = _ := by rw [Finset.mul_sum]

omit [DecidableEq ι] in
lemma support_value_smul (u : ι → ℝ) (c : ℝ) :
    ((∑ i, |(c • u) i|) + |∑ i, (c • u) i|) / 2 =
      |c| * (((∑ i, |u i|) + |∑ i, u i|) / 2) := by
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, ← Finset.mul_sum]
  rw [← mul_add, mul_div_assoc]

/-- Positive scalar images of the centered zonotope have the scaled support inequalities. -/
theorem scaled_centered_eq_support_halfspaces (c : ℝ) (hc : 0 < c) :
    (fun y : ι → ℝ => c • y) '' centered =
      {x | ∀ u : ι → ℝ, (∑ i, u i * x i) ≤
        c * (((∑ i, |u i|) + |∑ i, u i|) / 2)} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ u
    rw [coordinate_pairing_smul]
    exact mul_le_mul_of_nonneg_left (centered_support_le u y hy) hc.le
  · intro hx
    refine ⟨c⁻¹ • x, ?_, ?_⟩
    · rw [centered_eq_support_halfspaces]
      intro u
      rw [coordinate_pairing_smul]
      have h := mul_le_mul_of_nonneg_left (hx u) (inv_nonneg.mpr hc.le)
      simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using h
    · funext i
      change c * (c⁻¹ * x i) = x i
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

omit [DecidableEq ι] in
lemma scaled_centered_support_attained (u : ι → ℝ) (c : ℝ) :
    ∃ x ∈ (fun y : ι → ℝ => c • y) '' centered,
      (∑ i, u i * x i) = c * (((∑ i, |u i|) + |∑ i, u i|) / 2) := by
  obtain ⟨y, hy, heq⟩ := centered_support_attained u
  refine ⟨c • y, ⟨y, hy, rfl⟩, ?_⟩
  rw [coordinate_pairing_smul, heq]

end DiagonalZonotope

end

end OAI
