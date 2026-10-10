import OAI.Probability.BenjaminiSchramm.LayerMomentCauchy

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma ennreal_finset_cauchy {ι : Type*} (s : Finset ι) (r f g : ι → ℝ≥0∞)
    (hr : ∀ i ∈ s, r i ≠ ⊤) (hf : ∀ i ∈ s, f i ≠ ⊤) (hg : ∀ i ∈ s, g i ≠ ⊤)
    (ht : ∀ i ∈ s, (r i)^2 ≤ f i*g i) :
    (∑ i ∈ s, r i)^2 ≤ (∑ i ∈ s, f i)*(∑ i ∈ s, g i) := by
  apply (ENNReal.toReal_le_toReal (ENNReal.pow_ne_top (ENNReal.sum_ne_top.mpr hr))
    (ENNReal.mul_ne_top (ENNReal.sum_ne_top.mpr hf) (ENNReal.sum_ne_top.mpr hg))).mp
  rw [ENNReal.toReal_pow,ENNReal.toReal_sum hr,ENNReal.toReal_mul,
    ENNReal.toReal_sum hf,ENNReal.toReal_sum hg]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => ENNReal.toReal_nonneg)
  intro i hi
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top (hf i hi) (hg i hi)) (ht i hi)
  simpa only [ENNReal.toReal_pow,ENNReal.toReal_mul] using hh

lemma weighted_lintegral_support_cauchy {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (w : ι → ℝ≥0∞)
    (f : ι → Ω → ℝ≥0∞) (A : ι → Set Ω)
    (hw : ∀ i ∈ s, w i ≠ ⊤) (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hf : ∀ i ∈ s, Measurable (f i)) (hzero : ∀ i ∈ s, ∀ ω, ω ∉ A i → f i ω=0)
    (hmass : ∀ i ∈ s, μ (A i) ≠ ⊤)
    (hfirst : ∀ i ∈ s, (∫⁻ ω, f i ω ∂μ) ≠ ⊤)
    (hsecond : ∀ i ∈ s, (∫⁻ ω, (f i ω)^2 ∂μ) ≠ ⊤) :
    (∑ i ∈ s, w i*(∫⁻ ω, f i ω ∂μ))^2 ≤
      (∑ i ∈ s, w i*μ (A i))*(∑ i ∈ s, w i*(∫⁻ ω, (f i ω)^2 ∂μ)) := by
  apply ennreal_finset_cauchy s _ _ _
    (fun i hi => ENNReal.mul_ne_top (hw i hi) (hfirst i hi))
    (fun i hi => ENNReal.mul_ne_top (hw i hi) (hmass i hi))
    (fun i hi => ENNReal.mul_ne_top (hw i hi) (hsecond i hi))
  intro i hi
  calc
    _ = (w i)^2*(∫⁻ ω, f i ω ∂μ)^2 := mul_pow _ _ _
    _ ≤ (w i)^2*(μ (A i)*(∫⁻ ω, (f i ω)^2 ∂μ)) :=
      mul_le_mul' le_rfl (lintegral_support_cauchy μ (f i) (hf i hi) (A i) (hA i hi) (hzero i hi))
    _ = _ := by ring

end Percolation.BenjaminiSchramm

end

end OAI
