import Mathlib

namespace OAI

section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace CriticalPercolation
variable {X : Type*} [MeasurableSpace X]

lemma lintegral_fractional_fourth (μ : Measure X) (f h : X → ℝ≥0∞)
    (hf : AEMeasurable f μ) (hh : AEMeasurable h μ) (hh1 : ∀ x, h x≤1) :
    (∫⁻ x, f x*h x ∂μ)^4 ≤ (∫⁻ x, (f x)^4 ∂μ)*(∫⁻ x, h x ∂μ)^3 := by
  have hpq : (4:ℝ).HolderConjugate (4/3) := Real.holderConjugate_iff.mpr (by norm_num)
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf hh
  have P : (∫⁻ x, h x^(4/3:ℝ) ∂μ) ≤ ∫⁻ x, h x ∂μ :=
    lintegral_mono (fun x => ENNReal.rpow_le_self_of_le_one (hh1 x) (by norm_num))
  have H' : (∫⁻ x, f x*h x ∂μ) ≤
      (∫⁻ x, (f x)^4 ∂μ)^(1/4:ℝ)*(∫⁻ x, h x ∂μ)^(3/4:ℝ) := by
    calc _ ≤ _ := H
         _ ≤ _ := by
           norm_num only [show (1/(4/3:ℝ))=3/4 by norm_num,ENNReal.rpow_ofNat]
           gcongr
  have H4 := ENNReal.rpow_le_rpow H' (by norm_num : (0:ℝ)≤4)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ)≤4),
    ←ENNReal.rpow_mul,←ENNReal.rpow_mul] at H4
  simpa only [show (1/4:ℝ)*4=1 by norm_num,show (3/4:ℝ)*4=3 by norm_num,
    ENNReal.rpow_one,ENNReal.rpow_ofNat] using H4

end CriticalPercolation
end
end

end OAI
