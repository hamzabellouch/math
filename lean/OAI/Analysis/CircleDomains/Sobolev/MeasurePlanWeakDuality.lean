import OAI.Analysis.CircleDomains.Probability.CompactMeasureBarycenter
import OAI.Analysis.CircleDomains.Probability.MeasureFamilyModulusBasic
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace OAI

/-! A supported probability plan with an L² barycenter gives the lower
modulus bound. All admissible tests retain their extended values. -/
open Set Function Filter MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

lemma measureFamilyModulus_lower_of_barycenter
    {A Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) (K : A → FiniteMeasure Z) {S : Set (FiniteMeasure Z)}
    (P : ProbabilityMeasure S) (hsupp : ∀ᵐ v ∂(P : Measure S), v.val ∈ range K)
    {q : Z → ℝ≥0∞} (hq : Measurable q)
    (hbar : compactMeasureBarycenter P = σ.withDensity q)
    {c : ℝ≥0} (hc : 0 < c) (he : (∫⁻ z, q z^2 ∂σ) ≤ (c : ℝ≥0∞)⁻¹) :
    (c : ℝ≥0∞) ≤ measureFamilyModulus A Z σ K := by
  apply le_iInf
  intro h
  apply le_iInf
  intro hh
  apply le_iInf
  intro ha
  have hpay : (1 : ℝ≥0∞) ≤ ∫⁻ z, q z * h z ∂σ := by
    have hp : (1 : ℝ≥0∞) ≤ ∫⁻ v : S, (∫⁻ z, h z ∂(v.val : Measure Z)) ∂(P : Measure S) := by
      calc
        (1 : ℝ≥0∞) = ∫⁻ _v : S, 1 ∂(P : Measure S) := by simp
        _ ≤ _ := by
          apply lintegral_mono_ae
          filter_upwards [hsupp] with v hv
          obtain ⟨a,haeq⟩ := hv
          simpa only [← haeq] using ha a
    rw [← compactMeasureBarycenter_lintegral P hh,hbar,
      lintegral_withDensity_eq_lintegral_mul _ hq hh] at hp
    exact hp
  have hconj : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq σ hconj hq.aemeasurable hh.aemeasurable
  have hroot : (1 : ℝ≥0∞) ≤ (∫⁻ z, q z^2 ∂σ)^(1/2 : ℝ) *
      (∫⁻ z, h z^2 ∂σ)^(1/2 : ℝ) := by
    exact hpay.trans (by simpa only [Pi.mul_apply,ENNReal.rpow_two] using hcs)
  have hsqrt (x : ℝ≥0∞) : (x^(1/2 : ℝ))^2 = x := by
    rw [← ENNReal.rpow_two,← ENNReal.rpow_mul]
    norm_num
  have hsquare := pow_le_pow_left' hroot 2
  simp only [one_pow,mul_pow,hsqrt] at hsquare
  have hbound : (1 : ℝ≥0∞) ≤ (c : ℝ≥0∞)⁻¹ * ∫⁻ z, h z^2 ∂σ :=
    hsquare.trans (mul_le_mul_left he _)
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  calc
    (c : ℝ≥0∞) = c*1 := (mul_one _).symm
    _ ≤ c * ((c : ℝ≥0∞)⁻¹ * ∫⁻ z, h z^2 ∂σ) := mul_le_mul_right hbound _
    _ = _ := by rw [← mul_assoc,ENNReal.mul_inv_cancel hc0 ENNReal.coe_ne_top,one_mul]

end CircleDomainRigidity

end

end OAI
