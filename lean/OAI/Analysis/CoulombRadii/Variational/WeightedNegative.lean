import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.PoissonInterior

namespace OAI

section
section
open MeasureTheory Set Filter
noncomputable section
namespace NeutralAtom

lemma weighted_nonneg_integrable_of_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w Y G : X → ℝ} (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0≤w x)
    (hY : AEStronglyMeasurable Y μ) (hY0 : ∀ᵐ x ∂μ, 0≤Y x)
    (hGi : Integrable (fun x => w x*G x) μ) {A d : ℝ}
    (hbound : ∀ᵐ x ∂μ, w x≠0 → Y x≤A*G x+d) :
    Integrable (fun x => w x*Y x) μ := by
  apply ((hGi.const_mul A).add (hw.const_mul d)).mono' (hw.aestronglyMeasurable.mul hY)
  filter_upwards [hw0,hY0,hbound] with x hw hy hb
  change ‖w x*Y x‖≤A*(w x*G x)+d*w x
  rw [Real.norm_of_nonneg (mul_nonneg hw hy)]
  by_cases hz : w x=0
  · simp [hz]
  have H := mul_le_mul_of_nonneg_left (hb hz) hw
  change w x*Y x≤A*(w x*G x)+d*w x
  nlinarith

lemma weighted_integral_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w Y G : X → ℝ} (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0≤w x)
    (hY : AEStronglyMeasurable Y μ) (hY0 : ∀ᵐ x ∂μ, 0≤Y x)
    (hGi : Integrable (fun x => w x*G x) μ) {A d : ℝ}
    (hbound : ∀ᵐ x ∂μ, w x≠0 → Y x≤A*G x+d) :
    (∫ x, w x*Y x ∂μ)≤A*(∫ x, w x*G x ∂μ)+d*(∫ x, w x ∂μ) := by
  have H := integral_mono_ae (weighted_nonneg_integrable_of_le hw hw0 hY hY0 hGi hbound)
    ((hGi.const_mul A).add (hw.const_mul d)) (show ∀ᵐ x ∂μ,
      w x*Y x≤A*(w x*G x)+d*w x from ?_)
  · simpa only [Pi.add_apply,integral_add (hGi.const_mul A) (hw.const_mul d),integral_const_mul] using H
  · filter_upwards [hw0,hbound] with x hw hb
    by_cases hz : w x=0
    · simp [hz]
    nlinarith [mul_le_mul_of_nonneg_left (hb hz) hw]

lemma weighted_exception_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w Y G : X → ℝ} (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0≤w x)
    (hY : AEStronglyMeasurable Y μ) (hY0 : ∀ᵐ x ∂μ, 0≤Y x)
    (hGi : Integrable (fun x => w x*G x) μ) {A d : ℝ}
    (hbound : ∀ᵐ x ∂μ, w x≠0 → Y x≤A*G x+d) (B : Set X) (hB : MeasurableSet B) :
    (∫ x in B, w x*Y x ∂μ)≤A*(∫ x, w x*G x ∂μ)+d*(∫ x, w x ∂μ) := by
  have hi := weighted_nonneg_integrable_of_le hw hw0 hY hY0 hGi hbound
  apply le_trans _ (weighted_integral_le hw hw0 hY hY0 hGi hbound)
  rw [←integral_indicator hB]
  apply integral_mono_ae (hi.indicator hB) hi
  filter_upwards [hw0,hY0] with x hw hy
  by_cases hx : x∈B
  · simp only [indicator_of_mem hx,le_refl]
  · simp only [indicator_of_notMem hx]
    exact mul_nonneg hw hy

end NeutralAtom
end

end
end

end OAI
