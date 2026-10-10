import Mathlib
import OAI.Probability.GaussianInformation.Kernel.NoisyCharge

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
open Projection Projection.Support GaussianTools ReferenceGaussian RowConcat Scale Noise DriftTools.FiniteReference

lemma sample_joint_measurable {k d : ℕ} :
    Measurable (fun a : Ambient d × Observation k d => sampleEquiv a.1 a.2) := by
  have hP := continuous_projectVector (k := k) (d := d)
  unfold sampleEquiv
  dsimp
  fun_prop

lemma joint_reference_log {d N : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (κ : Observation (d/16) d → Fin N → ℝ≥0∞)
    (hκ : Measurable (Function.uncurry κ)) (hκ1 : ∀ z,∑ w,κ z w=1)
    (L : ℕ) (hL : 0 < L)
    (hcut : ENNReal.ofReal (H*(9*3^d)*(4:ℝ)^(d-1))*
      ENNReal.ofReal ((2:ℝ)^(2*(d/16)+1))*ENNReal.ofReal ((1/2:ℝ)^L) ≤ 1)
    {η : ℝ} (hη : 0 < η) (hηL : η ≤ radius L) :
    Integrable (fun t : Ambient d × Observation (d/16) d × Fin N =>
      Real.log (PairReference.density ν (fun j : Fin L => radius j) t.2.1.1.1 t.2.1.1.2 t.2.1.2.1 t.2.1.2.2))
      (joint ν (observationBase (d/16) d) (observationKernel η) κ) ∧
    B ν-10*(d:ℝ)-2*Real.log ((L:ℝ)+2) ≤
      ∫ t : Ambient d × Observation (d/16) d × Fin N,
        Real.log (PairReference.density ν (fun j : Fin L => radius j) t.2.1.1.1 t.2.1.1.2 t.2.1.2.1 t.2.1.2.2)
        ∂joint ν (observationBase (d/16) d) (observationKernel η) κ := by
  have := sampling_probability (d/16) d hη
  have := noise_probability (d/16) hη
  have : IsProbabilityMeasure (gaussianRows (d/16) d) := by unfold gaussianRows; infer_instance
  let q : Observation (d/16) d → ℝ := fun z =>
    Real.log (PairReference.density ν (fun j : Fin L => radius j) z.1.1 z.1.2 z.2.1 z.2.2)
  have hq : Measurable q := (PairReference.density_measurable ν _).log
  let g : Ambient d × Observation (d/16) d → ℝ := fun a => q (sampleEquiv a.1 a.2)
  have hg : Measurable g := hq.comp sample_joint_measurable
  have hnorm : ∀ᵐ s ∂ν,‖s‖=1 :=
    (Measure.absolutelyContinuous_of_le_smul hν).ae_le (Sphere.ae_unit_norm (by omega : 0 < d))
  obtain ⟨M,_,hb⟩ := log_mixture_uniform_bound (p := 2*(d/16)) hL ν
    (fun j : Fin L => radius j) (fun j => radius_pos j) (by norm_num : (0:ℝ) ≤ 2) hη.le
  have hiE : Integrable (fun t : Observation (d/16) d => matEnergy (join (d/16) t.1))
      (samplingLaw (d/16) d η) := (integrable_pairEnergy (d/16) d).comp_fst _
  have hi : Integrable g (ν.prod (samplingLaw (d/16) d η)) := by
    refine (((integrable_const 1).add hiE).comp_snd ν).const_mul M |>.mono' hg.aestronglyMeasurable ?_
    have hs : ∀ᵐ a ∂ν.prod (samplingLaw (d/16) d η),‖a.1‖=1 :=
      measurePreserving_fst.quasiMeasurePreserving.ae hnorm
    have ht : ∀ᵐ a ∂ν.prod (samplingLaw (d/16) d η),∀ i,|join (d/16) a.2.2 i| ≤ η :=
      measurePreserving_snd.quasiMeasurePreserving.ae (sampling_noise_support (d/16) d hη)
    filter_upwards [hs,ht] with a hs ht
    have hsupport : ∀ᵐ u ∂ν,u ∈ closedBall a.1 2 := by
      filter_upwards [hnorm] with u hu
      rw [mem_closedBall,dist_eq_norm]
      exact (norm_sub_le _ _).trans (by rw [hu,hs]; norm_num)
    change |q (sampleEquiv a.1 a.2)| ≤ M*(1+matEnergy (join (d/16) a.2.1))
    dsimp only [q]
    rw [sample_density]
    exact hb a.1 hsupport (join (d/16) a.2.1) (join (d/16) a.2.2) ht
  have hK := observationKernel_measurable (k := d/16) (d := d) η
  have he (s : Ambient d) : (∫⁻ z,observationKernel η z s*‖q z‖ₑ ∂observationBase (d/16) d)=
      ∫⁻ t,‖g (s,t)‖ₑ ∂samplingLaw (d/16) d η := by
    have hKs : Measurable (fun z : Observation (d/16) d => observationKernel η z s) := by fun_prop
    calc
      _ = ∫⁻ z,‖q z‖ₑ ∂(observationBase (d/16) d).withDensity (fun z => observationKernel η z s) := by
        simpa only [Pi.mul_apply] using (lintegral_withDensity_eq_lintegral_mul (observationBase (d/16) d) hKs hq.enorm).symm
      _ = _ := ((sample_measurePreserving hη s).lintegral_comp hq.enorm).symm
  have hiq : Integrable (fun t : Ambient d × Observation (d/16) d × Fin N => q t.2.1)
      (joint ν (observationBase (d/16) d) (observationKernel η) κ) := by
    apply joint_observation_integrable ν _ _ κ hK hκ hκ1 (fun a => q a.2) (hq.comp measurable_snd)
    simp_rw [he]
    rw [← lintegral_prod _ hg.enorm.aemeasurable]
    exact hi.hasFiniteIntegral
  refine ⟨hiq,?_⟩
  have hidentity := joint_observation_integral ν (observationBase (d/16) d) (observationKernel η) κ
    hK hκ (observationKernel_ne_top hη) hκ1 (fun a : Ambient d × Observation (d/16) d => q a.2) hiq
  change B ν-10*(d:ℝ)-2*Real.log ((L:ℝ)+2) ≤ ∫ t,q t.2.1 ∂joint ν _ _ κ
  rw [hidentity]
  have hiqν : Integrable (fun s => ∫ z,q z ∂(observationBase (d/16) d).withDensity (fun z => observationKernel η z s)) ν :=
    hi.integral_prod_left.congr (ae_of_all _ (fun s => (sample_integral hη s q).symm))
  have hiJ := Coercivity.integrable_log_J hd ν ⟨H,hH,hν⟩ ν hnorm
  have hl := integral_mono_ae ((hiJ.sub (integrable_const (10*(d:ℝ)))).sub (integrable_const (2*Real.log ((L:ℝ)+2)))) hiqν
    (by
      filter_upwards [hnorm] with s hs
      exact noisy_reference_J_lower hd ν hH hν s hs L hL hcut hη hηL)
  simp only [Pi.sub_apply] at hl
  rw [integral_sub (show Integrable (fun s => Real.log (J ν s).toReal-10*(d:ℝ)) ν from hiJ.sub (integrable_const _)) (integrable_const (2*Real.log ((L:ℝ)+2))),
    integral_sub hiJ (integrable_const (10*(d:ℝ)))] at hl
  simpa only [integral_const,probReal_univ,one_smul,B] using hl
end KernelPotential.NoisyReference

end OAI
