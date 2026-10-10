import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.BlowupMeasure

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal Pointwise

theorem blowupMeasure_support_image {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    (blowupMeasure n μ a r).support = (fun y => r⁻¹ • (y - a)) '' μ.support := by
  ext x
  constructor
  · intro hx
    refine ⟨a + r • x, (blowupMeasure_support_iff n μ a x r hr).mp hx, ?_⟩
    change r⁻¹ • ((a + r • x) - a) = x
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  · rintro ⟨y, hy, rfl⟩
    apply (blowupMeasure_support_iff n μ a _ r hr).mpr
    have heq : a + r • (r⁻¹ • (y - a)) = y := by
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      abel
    rw [heq]
    exact hy

theorem blowupMeasure_ediam_support {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    ediam (blowupMeasure n μ a r).support = ENNReal.ofReal r⁻¹ * ediam μ.support := by
  have himage : (fun y : Ambient d => r⁻¹ • (y - a)) '' μ.support =
      r⁻¹ • ((fun y : Ambient d => y - a) '' μ.support) := by
    rw [← Set.image_smul, Set.image_image]
  have htranslate : Isometry (fun y : Ambient d => y - a) := by
    apply Isometry.of_dist_eq
    intro x y
    exact dist_sub_right x y a
  rw [blowupMeasure_support_image n μ a r hr, himage, ediam_smul₀,
    htranslate.ediam_image μ.support]
  change (‖r⁻¹‖₊ : ℝ≥0∞) * ediam μ.support = _
  rw [← ENNReal.ofReal_coe_nnreal]
  simp only [coe_nnnorm, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]

theorem blowupMeasure_ediam_support_mul {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    ENNReal.ofReal r * ediam (blowupMeasure n μ a r).support = ediam μ.support := by
  rw [blowupMeasure_ediam_support n μ a r hr, ← mul_assoc,
    ← ENNReal.ofReal_mul hr.le, mul_inv_cancel₀ hr.ne', ENNReal.ofReal_one, one_mul]

theorem blowupMeasure_admissibleRadius_iff {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) :
    AdmissibleRadius (blowupMeasure n μ a r) R ↔ AdmissibleRadius μ (r * R) := by
  constructor
  · intro hR
    refine ⟨mul_pos hr hR.1, ?_⟩
    calc
      ENNReal.ofReal (r * R) = ENNReal.ofReal r * ENNReal.ofReal R := ENNReal.ofReal_mul hr.le
      _ ≤ ENNReal.ofReal r * ediam (blowupMeasure n μ a r).support := mul_le_mul_right hR.2 _
      _ = ediam μ.support := blowupMeasure_ediam_support_mul n μ a r hr
  · intro hR
    refine ⟨(mul_pos_iff_of_pos_left hr).mp hR.1, ?_⟩
    rw [blowupMeasure_ediam_support n μ a r hr]
    calc
      ENNReal.ofReal R = ENNReal.ofReal r⁻¹ * ENNReal.ofReal (r * R) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
        congr 1
        field_simp
      _ ≤ ENNReal.ofReal r⁻¹ * ediam μ.support := mul_le_mul_right hR.2 _

theorem blowupMeasure_lower_admissible {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r C : ℝ) (hr : 0 < r)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, AdmissibleRadius μ R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R)) :
    ∀ x ∈ (blowupMeasure n μ a r).support, ∀ R : ℝ, AdmissibleRadius (blowupMeasure n μ a r) R →
      ENNReal.ofReal (R ^ n / C) ≤ blowupMeasure n μ a r (ball x R) := by
  intro x hx R hR
  rw [blowupMeasure_ball n μ a x r R hr]
  have h := hlower (a + r • x) ((blowupMeasure_support_iff n μ a x r hr).mp hx)
    (r * R) ((blowupMeasure_admissibleRadius_iff n μ a r R hr).mp hR)
  calc
    _ = ENNReal.ofReal ((r ^ n)⁻¹) * ENNReal.ofReal ((r * R) ^ n / C) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (r ^ n)⁻¹)]
      congr 1
      rw [mul_pow]
      field_simp
    _ ≤ _ := mul_le_mul_right h _

end

end RieszRectifiability

end OAI
