import OAI.Analysis.FiniteFactor.Convolution
import OAI.Analysis.FiniteFactor.TailEstimate

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Cauchy--Schwarz for genuinely infinite nonnegative coefficient series. -/
theorem nonnegative_series_cauchy_schwarz {ι : Type*} (f g : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hfs : Summable (fun i => f i^2)) (hgs : Summable (fun i => g i^2)) :
    Summable (fun i => f i*g i) ∧
    (∑' i, f i*g i) ≤ Real.sqrt (∑' i, f i^2)*Real.sqrt (∑' i, g i^2) := by
  have hp : Real.HolderConjugate 2 2 := by norm_num [Real.holderConjugate_iff]
  have hF : 0 ≤ ∑' i, f i^2 := tsum_nonneg (fun i => sq_nonneg _)
  have hG : 0 ≤ ∑' i, g i^2 := tsum_nonneg (fun i => sq_nonneg _)
  have hsf : HasSum (fun i => f i^(2 : ℝ)) ((Real.sqrt (∑' i, f i^2))^(2 : ℝ)) := by
    simpa only [Real.rpow_two,Real.sq_sqrt hF] using hfs.hasSum
  have hsg : HasSum (fun i => g i^(2 : ℝ)) ((Real.sqrt (∑' i, g i^2))^(2 : ℝ)) := by
    simpa only [Real.rpow_two,Real.sq_sqrt hG] using hgs.hasSum
  obtain ⟨C,_,hC,hs⟩ := Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg hp
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hf hg hsf hsg
  exact ⟨hs.summable,hs.tsum_eq ▸ hC⟩

/-- Probability-space Cauchy--Schwarz after the pointwise series estimate.
Equivalent to the product-with-counting-measure argument; no independence or
finite truncation is assumed. -/
theorem countable_error_integral_le {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (f g : ι → Ω → ℝ) (δ : ℝ)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hf0 : ∀ i ω, 0 ≤ f i ω) (hg0 : ∀ i ω, 0 ≤ g i ω)
    (hfs : ∀ᵐ ω ∂μ, Summable (fun i => f i ω^2))
    (hgs : ∀ᵐ ω ∂μ, Summable (fun i => g i ω^2))
    (hfi : Integrable (fun ω => ∑' i, f i ω^2) μ)
    (hfm : (∫ ω, (∑' i, f i ω^2) ∂μ) ≤ δ)
    (hg1 : ∀ᵐ ω ∂μ, (∑' i, g i ω^2) ≤ 1) :
    Integrable (fun ω => ∑' i, f i ω*g i ω) μ ∧
    (∫ ω, (∑' i, f i ω*g i ω) ∂μ) ≤ Real.sqrt δ := by
  let F := fun ω => ∑' i, f i ω^2
  let S := fun ω => ∑' i, f i ω*g i ω
  have hF0 (ω) : 0 ≤ F ω := tsum_nonneg (fun i => sq_nonneg _)
  have hFm : Measurable F := Measurable.tsum (fun i => (hf i).pow_const 2)
  have hSm : Measurable S := Measurable.tsum (fun i => (hf i).mul (hg i))
  have hS0 (ω) : 0 ≤ S ω := tsum_nonneg (fun i => mul_nonneg (hf0 i ω) (hg0 i ω))
  have hFroot : MemLp (fun ω => Real.sqrt (F ω)) 2 μ := by
    apply (memLp_two_iff_integrable_sq (hFm.sqrt.aestronglyMeasurable)).mpr
    simpa only [Real.sq_sqrt (hF0 _)] using hfi
  have hS : ∀ᵐ ω ∂μ, S ω ≤ Real.sqrt (F ω) := by
    filter_upwards [hfs,hgs,hg1] with ω hs ht h1
    have hh := (nonnegative_series_cauchy_schwarz (fun i => f i ω) (fun i => g i ω)
      (fun i => hf0 i ω) (fun i => hg0 i ω) hs ht).2
    apply hh.trans
    simpa only [Real.sqrt_one,mul_one] using
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) (Real.sqrt_nonneg (F ω))
  have hSi : Integrable S μ := (hFroot.integrable (by norm_num)).mono'
    hSm.aestronglyMeasurable (hS.mono fun ω h => by rwa [Real.norm_of_nonneg (hS0 ω)])
  refine ⟨hSi,?_⟩
  have hh := integral_mul_le_sqrt_of_square_bounds hFroot (memLp_const (1 : ℝ))
    (Eventually.of_forall fun ω => Real.sqrt_nonneg (F ω)) (Eventually.of_forall fun _ => zero_le_one)
    (by simpa only [Real.sq_sqrt (hF0 _)] using hfm)
    (by simp : (∫ _ω : Ω, (1 : ℝ)^2 ∂μ) ≤ 1)
  apply (integral_mono_ae hSi (hFroot.integrable (by norm_num)) hS).trans
  simpa only [mul_one] using hh

end
end FiniteFactor

end OAI
