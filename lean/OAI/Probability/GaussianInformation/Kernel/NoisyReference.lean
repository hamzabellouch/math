import Mathlib
import OAI.Probability.GaussianInformation.Kernel.DriftCutoff

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal
namespace KernelPotential.NoisyReference
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection Projection.Support Noise ReferenceGaussian GaussianTools RowConcat Scale

lemma sample_density {k d L : ℕ} (ν : Measure (Ambient d)) (r : Fin L → ℝ)
    (s : Ambient d) (t : Observation k d) :
    PairReference.density ν r (sampleEquiv s t).1.1 (sampleEquiv s t).1.2
      (sampleEquiv s t).2.1 (sampleEquiv s t).2.2 =
      mixture ν r (join k t.1) (applyRows (join k t.1) s+join k t.2) := by
  change mixture ν r (join k t.1) (join k (applyRows t.1.1 s+t.2.1,applyRows t.1.2 s+t.2.2))=_
  rw [join_add,show join k (applyRows t.1.1 s,applyRows t.1.2 s)=applyRows (join k t.1) s from join_rows k d _ _ s]

lemma pair_noise_support (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᵐ e ∂(noiseLaw k η).prod (noiseLaw k η),∀ i,|join k e i| ≤ η := by
  have := noise_probability k hη
  have h1 : ∀ᵐ e ∂(noiseLaw k η).prod (noiseLaw k η),e.1 ∈ closedBox 0 η :=
    measurePreserving_fst.quasiMeasurePreserving.ae (noise_support k η)
  have h2 : ∀ᵐ e ∂(noiseLaw k η).prod (noiseLaw k η),e.2 ∈ closedBox 0 η :=
    measurePreserving_snd.quasiMeasurePreserving.ae (noise_support k η)
  filter_upwards [h1,h2] with e h1 h2
  apply join_bound k e.1 e.2 (fun x : ℝ => |x| ≤ η)
  · simpa only [closedBox,Set.mem_ofPred_eq,Pi.zero_apply,sub_zero] using h1
  · simpa only [closedBox,Set.mem_ofPred_eq,Pi.zero_apply,sub_zero] using h2

lemma sampling_noise_support (k d : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᵐ t ∂samplingLaw k d η,∀ i,|join k t.2 i| ≤ η := by
  have := noise_probability k hη
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  exact measurePreserving_snd.quasiMeasurePreserving.ae (pair_noise_support k hη)

lemma integrable_pairEnergy (k d : ℕ) :
    Integrable (fun t : (Mat k d) × (Mat k d) => matEnergy (join k t))
      ((gaussianRows k d).prod (gaussianRows k d)) := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  exact (join_measurePreserving k (scalarRow d)).integrable_comp_of_integrable integrable_matEnergy

lemma sampling_log_integrable {k d L : ℕ} (hL : 0 < L)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] (r : Fin L → ℝ) (hr : ∀ j,0 < r j)
    (s : Ambient d) {R η : ℝ} (hR : 0 ≤ R) (hη : 0 < η)
    (hs : ∀ᵐ u ∂ν,u ∈ closedBall s R) :
    Integrable (fun t : Observation k d => Real.log (PairReference.density ν r
      (sampleEquiv s t).1.1 (sampleEquiv s t).1.2 (sampleEquiv s t).2.1 (sampleEquiv s t).2.2))
      (samplingLaw k d η) := by
  have := noise_probability k hη
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  obtain ⟨M,_,hb⟩ := log_mixture_uniform_bound (p := 2*k) hL ν r hr hR hη.le
  have hm : Measurable (fun t : Observation k d => Real.log (PairReference.density ν r
      (sampleEquiv s t).1.1 (sampleEquiv s t).1.2 (sampleEquiv s t).2.1 (sampleEquiv s t).2.2)) := by
    have hD := PairReference.density_measurable (k := k) ν r
    have hS := (sampleEquiv (k := k) s).measurable
    exact Real.measurable_log.comp (hD.comp hS)
  refine ((integrable_const 1).add ((integrable_pairEnergy k d).comp_fst _)).const_mul M |>.mono' hm.aestronglyMeasurable ?_
  filter_upwards [sampling_noise_support k d hη] with t ht
  rw [Real.norm_eq_abs,sample_density]
  exact hb s hs (join k t.1) (join k t.2) ht

lemma q_probability {k d L : ℕ} (hL : 0 < L) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] (r : Fin L → ℝ) (hr : ∀ j,0 < r j) :
    (∫⁻ z : Observation k d,ENNReal.ofReal (PairReference.density ν r z.1.1 z.1.2 z.2.1 z.2.2)
      ∂observationBase k d)=1 := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  rw [observationBase,lintegral_prod _ (PairReference.density_measurable ν r).ennreal_ofReal.aemeasurable]
  simp only [PairReference.density_probability hL ν r hr,lintegral_one,measure_univ]

lemma noisy_reference_J_lower {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) (hs : ‖s‖=1)
    (L : ℕ) (hL : 0 < L)
    (hcut : ENNReal.ofReal (H*(9*3^d)*(4:ℝ)^(d-1))*
      ENNReal.ofReal ((2:ℝ)^(2*(d/16)+1))*ENNReal.ofReal ((1/2:ℝ)^L) ≤ 1)
    {η : ℝ} (hη : 0 < η) (hηL : η ≤ radius L) :
    Real.log (J ν s).toReal-10*(d:ℝ)-2*Real.log ((L:ℝ)+2) ≤
      (∫ z : Observation (d/16) d,Real.log (PairReference.density ν (fun j : Fin L => radius j)
        z.1.1 z.1.2 z.2.1 z.2.2)
        ∂(observationBase (d/16) d).withDensity (fun z => observationKernel η z s)) := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  have := noise_probability (d/16) hη
  have : IsProbabilityMeasure (gaussianRows (d/16) d) := by unfold gaussianRows; infer_instance
  have hiSupport : ∀ᵐ u ∂ν,u ∈ closedBall s 2 := by
    filter_upwards [(Measure.absolutelyContinuous_of_le_smul hν).ae_le (Sphere.ae_unit_norm (by omega : 0 < d))] with u hu
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by rw [hu,hs]; norm_num)
  have hi := sampling_log_integrable (k := d/16) hL ν (fun j : Fin L => radius j) (fun j => radius_pos j)
    s (by norm_num : (0:ℝ) ≤ 2) hη hiSupport
  rw [sample_integral hη s,samplingLaw,integral_prod _ hi,integral_integral_swap hi]
  have hir := hi.integral_prod_right
  calc
    _ = ∫ _e : (Fin (d/16) → ℝ) × (Fin (d/16) → ℝ),
        Real.log (J ν s).toReal-10*(d:ℝ)-2*Real.log ((L:ℝ)+2)
        ∂(noiseLaw (d/16) η).prod (noiseLaw (d/16) η) := by simp
    _ ≤ _ := by
      apply integral_mono_ae (integrable_const _) hir
      filter_upwards [pair_noise_support (d/16) hη] with e he
      have he' : ∀ i,|join (d/16) e i| ≤ radius L := fun i => (he i).trans hηL
      have h := reference_J_lower hd ν hH hν s hs L hL hcut _ he'
      have hrw : (∫ XZ : Mat (d/16) d × Mat (d/16) d,
          Real.log (PairReference.density ν (fun j : Fin L => radius j)
            (sampleEquiv s (XZ,e)).1.1 (sampleEquiv s (XZ,e)).1.2
            (sampleEquiv s (XZ,e)).2.1 (sampleEquiv s (XZ,e)).2.2)
          ∂(gaussianRows (d/16) d).prod (gaussianRows (d/16) d))=
          ∫ X : Mat (2*(d/16)) d,Real.log (mixture ν (fun j : Fin L => radius j) X
            (applyRows X s+join (d/16) e)) ∂Measure.pi (fun _ : Fin (2*(d/16)) => scalarRow d) := by
        simp only [sample_density]
        exact (join_measurePreserving (d/16) (scalarRow d)).integral_comp'
          (fun X : Mat (2*(d/16)) d => Real.log (mixture ν (fun j : Fin L => radius j) X
            (applyRows X s+join (d/16) e)))
      rw [hrw]
      exact h
end KernelPotential.NoisyReference

end OAI
