import Mathlib
import OAI.Probability.GaussianInformation.Kernel.NoisyMoments

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.DriftTools.FiniteReference
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
lemma kernel_average_measurable (Λ : Measure β) [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (hK : Measurable (Function.uncurry K))
    (hKfin : ∀ z s,K z s ≠ ∞) (g : β → ℝ) (hg : Measurable g) :
    Measurable (fun s => ∫ z,g z ∂Λ.withDensity (fun z => K z s)) := by
  have hm : Measurable (fun t : α × β => (K t.2 t.1).toReal*g t.2) := by fun_prop
  have hh := (hm.stronglyMeasurable.integral_prod_right' (ν := Λ)).measurable
  convert hh using 1
  ext s
  have hKs : Measurable (fun z => K z s) := hK.comp (measurable_id.prodMk measurable_const)
  rw [integral_withDensity_eq_integral_toReal_smul hKs
    (ae_of_all _ (fun z => lt_top_iff_ne_top.mpr (hKfin z s)))]
  simp only [smul_eq_mul]

lemma kernel_average_integrable (ν : Measure α) [IsFiniteMeasure ν] (Λ : Measure β) [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (hK : Measurable (Function.uncurry K))
    (hKfin : ∀ z s,K z s ≠ ∞) (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1)
    (g : β → ℝ) (hg : Measurable g) {M : ℝ} (hgM : ∀ z,‖g z‖ ≤ M) :
    Integrable (fun s => ∫ z,g z ∂Λ.withDensity (fun z => K z s)) ν := by
  refine Integrable.of_bound (kernel_average_measurable Λ K hK hKfin g hg).aestronglyMeasurable M ?_
  filter_upwards [] with s
  have : IsProbabilityMeasure (Λ.withDensity (fun z => K z s)) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,hK1]
  simpa using norm_integral_le_of_norm_le_const (μ := Λ.withDensity (fun z => K z s))
    (ae_of_all _ hgM)
end KernelPotential.DriftTools.FiniteReference

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference EntropySupport Coercivity Sphere
noncomputable def postCharge {d N : ℕ} (ν : Measure (Ambient d))
    (rule : PositiveRule (d/16) d N) (η : ℝ) (z : Observation (d/16) d) (w : Fin N) : ℝ :=
  Real.log (1+(projectedReference (post ν (rule.response η w)) η z.1.1 z.1.2 z.2.1 z.2.2).toReal)

lemma measurable_postCharge {d N : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    {H : ℝ} (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) :
    Measurable (Function.uncurry (postCharge ν rule η)) := by
  apply measurable_from_prod_countable_left
  intro w
  have := rule.post_prob hη ν w
  have hnorm : ∀ᵐ s ∂ν,‖s‖=1 := (Measure.absolutelyContinuous_of_le_smul hν).ae_le (ae_unit_norm (by omega : 0 < d))
  have := Reweight.rho_finite (post ν (rule.response η w)) (withDensity_absolutelyContinuous _ _ |>.ae_le hnorm)
  exact (measurable_const.add (projectedReference_measurable (post ν (rule.response η w)) η).ennreal_toReal).log

lemma postCharge_uniform_bound {d N : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ z w,0 ≤ postCharge ν rule η z w ∧ postCharge ν rule η z w ≤ M := by
  classical
  have hh (w : Fin N) : ∃ M : ℝ,0 ≤ M ∧ ∀ z,0 ≤ postCharge ν rule η z w ∧ postCharge ν rule η z w ≤ M := by
    have := rule.post_prob hη ν w
    have hb := post_bounded ν hH hν (rule.response η w) (fun s => (rule.response_bounds hη w s).2) (rule.mass_pos hη ν w)
    have hnorm : ∀ᵐ s ∂post ν (rule.response η w),‖s‖=1 :=
      (Measure.absolutelyContinuous_of_le_smul hb).ae_le (ae_unit_norm (by omega : 0 < d))
    exact projected_log_bounded (post ν (rule.response η w)) hnorm hη
  choose M hM hb using hh
  refine ⟨∑ w,M w,Finset.sum_nonneg (fun w _ => hM w),fun z w => ⟨(hb w z).1,(hb w z).2.trans ?_⟩⟩
  exact Finset.single_le_sum (fun v _ => hM v) (Finset.mem_univ w)

lemma postCharge_pointwise {d N : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) (w : Fin N)
    {s : Ambient d} (hs : ‖s‖=1) :
    (∫ z : Observation (d/16) d,rule.prob (z.1.1,z.2.1) w*postCharge ν rule η z w
      ∂(observationBase (d/16) d).withDensity (fun z => observationKernel η z s)) ≤
      -xlog (rule.response η w s)/(d/16:ℕ)+rule.response η w s*
        (10*(d:ℝ)+Real.log ((DriftCutoff.level d (H/mass ν (rule.response η w)):ℝ)+2)) := by
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have ha := rule.mass_pos hη ν w
  have hHdiv : 1 ≤ H/mass ν (rule.response η w) :=
    (le_div_iff₀ ha).mpr (by simpa using (rule.mass_le_one hη ν w).trans hH)
  have := rule.post_prob hη ν w
  have hpost := post_bounded ν hHp hν _ (fun s => (rule.response_bounds hη w s).2) ha
  have hc := noisy_weighted_projection hd (post ν (rule.response η w)) (div_pos hHp ha) hpost s hs
    (DriftCutoff.level d (H/mass ν (rule.response η w))) (DriftCutoff.moment_cut d hd hHdiv)
    hη (fun t => rule.prob t w) (rule.measurable w) (fun t => rule.nonneg t w) (fun t => rule.le_one t w)
  simpa only [← rule.response_average hη,xlog,postCharge,neg_mul] using hc

lemma integrable_postCharge_average {d N : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hHp : 0 < H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) (w : Fin N) :
    Integrable (fun s => ∫ z : Observation (d/16) d,rule.prob (z.1.1,z.2.1) w*postCharge ν rule η z w
      ∂(observationBase (d/16) d).withDensity (fun z => observationKernel η z s)) ν := by
  obtain ⟨M,hM,hMb⟩ := postCharge_uniform_bound hd ν hHp hν rule hη
  have hm1 : Measurable (fun z : Observation (d/16) d => rule.prob (z.1.1,z.2.1) w) :=
    (rule.measurable w).comp (show Measurable (fun z : Observation (d/16) d => (z.1.1,z.2.1)) from measurable_fst.fst.prodMk measurable_snd.fst)
  have hm2 : Measurable (fun z : Observation (d/16) d => postCharge ν rule η z w) :=
    (measurable_postCharge hd ν hν rule hη).comp (f := fun z : Observation (d/16) d => (z,w)) (show Measurable (fun z : Observation (d/16) d => (z,w)) from measurable_id.prodMk measurable_const)
  have hg : Measurable (fun z : Observation (d/16) d => rule.prob (z.1.1,z.2.1) w*postCharge ν rule η z w) := hm1.mul hm2
  have hgb (z : Observation (d/16) d) : ‖rule.prob (z.1.1,z.2.1) w*postCharge ν rule η z w‖ ≤ M := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (rule.nonneg _ w) (hMb z w).1)]
    exact (mul_le_mul_of_nonneg_right (rule.le_one _ w) (hMb z w).1).trans (by simpa using (hMb z w).2)
  exact kernel_average_integrable ν (observationBase (d/16) d) (observationKernel η)
    (observationKernel_measurable η) (observationKernel_ne_top hη) (observationKernel_probability hη) _ hg hgb

lemma integrated_postCharge {d N : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 1 ≤ H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (rule : PositiveRule (d/16) d N) {η : ℝ} (hη : 0 < η) (w : Fin N) :
    (∫ s,∫ z : Observation (d/16) d,rule.prob (z.1.1,z.2.1) w*postCharge ν rule η z w
      ∂(observationBase (d/16) d).withDensity (fun z => observationKernel η z s) ∂ν) ≤
      -(∫ s,xlog (rule.response η w s) ∂ν)/(d/16:ℕ)+
        mass ν (rule.response η w)*(10*(d:ℝ)+Real.log ((DriftCutoff.level d (H/mass ν (rule.response η w)):ℝ)+2)) := by
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have ha := rule.mass_pos hη ν w
  have ha1 := rule.mass_le_one hη ν w
  have hHdiv : 1 ≤ H/mass ν (rule.response η w) := (le_div_iff₀ ha).mpr (by simpa using ha1.trans hH)
  have := rule.post_prob hη ν w
  have hpost := post_bounded ν hHp hν (rule.response η w) (fun s => (rule.response_bounds hη w s).2) ha
  have hnorm : ∀ᵐ s ∂ν,‖s‖=1 :=
    (Measure.absolutelyContinuous_of_le_smul hν).ae_le (ae_unit_norm (by omega : 0 < d))
  have hi := integrable_postCharge_average hd ν hHp hν rule hη w
  have hir := integrable_rule ν _ (rule.measurable_response η w)
    (fun s => rule.lower_pos.le.trans (rule.response_bounds hη w s).1) (fun s => (rule.response_bounds hη w s).2)
  have hix := integrable_xlog_bounded ν _ (rule.measurable_response η w)
    (fun s => rule.lower_pos.le.trans (rule.response_bounds hη w s).1) (fun s => (rule.response_bounds hη w s).2)
  let L := DriftCutoff.level d (H/mass ν (rule.response η w))
  have hh := integral_mono_ae hi ((hix.neg.div_const (d/16:ℕ)).add (hir.mul_const (10*(d:ℝ)+Real.log ((L:ℝ)+2)))) (by
    filter_upwards [hnorm] with s hs
    exact postCharge_pointwise hd ν hH hν rule hη w hs)
  have hi1 : Integrable (fun s => -xlog (rule.response η w s)/(d/16:ℕ)) ν := hix.neg.div_const _
  have hi2 : Integrable (fun s => rule.response η w s*(10*(d:ℝ)+Real.log ((L:ℝ)+2))) ν := hir.mul_const _
  change _ ≤ ∫ s, -xlog (rule.response η w s)/(d/16:ℕ)+rule.response η w s*(10*(d:ℝ)+Real.log ((L:ℝ)+2)) ∂ν at hh
  rw [integral_add hi1 hi2,integral_div,integral_neg,integral_mul_const] at hh
  exact hh
end KernelPotential.NoisyDrift

end OAI
