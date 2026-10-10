import Mathlib
import OAI.Probability.GaussianInformation.Kernel.SimplexApproximation

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian Reweight Sphere DriftTools

lemma sampling_noise_mem {k d : ℕ} {η : ℝ} (hη : 0 < η) :
    ∀ᵐ t ∂samplingLaw k d η,t.2.1 ∈ closedBox 0 η ∧ t.2.2 ∈ closedBox 0 η := by
  have := noise_probability k hη
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have h1 : ∀ᵐ e ∂(noiseLaw k η).prod (noiseLaw k η),e.1 ∈ closedBox 0 η :=
    measurePreserving_fst.quasiMeasurePreserving.ae (noise_support k η)
  have h2 : ∀ᵐ e ∂(noiseLaw k η).prod (noiseLaw k η),e.2 ∈ closedBox 0 η :=
    measurePreserving_snd.quasiMeasurePreserving.ae (noise_support k η)
  exact measurePreserving_snd.quasiMeasurePreserving.ae (h1.and h2)

lemma projectedReference_real_bound {d k : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν,‖s‖=1) {η : ℝ} (hη : 0 < η) (z : Observation k d) :
    (projectedReference ν η z.1.1 z.1.2 z.2.1 z.2.2).toReal ≤
      (boxScale k η).toReal^2*2^(2*(d/16)) := by
  have hb := (rho_le ν hν Set.univ).trans_eq (by simp :
    ((ENNReal.ofReal ((2:ℝ)^(2*(d/16)))) • ν) Set.univ=ENNReal.ofReal ((2:ℝ)^(2*(d/16))))
  have hc := (projectedReference_le ν η z.1.1 z.1.2 z.2.1 z.2.2).trans (mul_le_mul_right hb _)
  apply (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top (boxScale_ne_top k hη)) ENNReal.ofReal_ne_top) hc).trans_eq
  simp [ENNReal.toReal_mul,ENNReal.toReal_pow]

lemma projectedReference_finite {d k : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν,‖s‖=1) {η : ℝ} (hη : 0 < η) (z : Observation k d) :
    projectedReference ν η z.1.1 z.1.2 z.2.1 z.2.2 ≠ ∞ := by
  have := rho_finite ν hν
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (boxScale_ne_top k hη)) (measure_ne_top _ _))
    (projectedReference_le ν η z.1.1 z.1.2 z.2.1 z.2.2)

lemma mixedCube_real_bound {d k : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ u ∂ν,‖u‖=1) (s : Ambient d) {η : ℝ} (hη : 0 < η) (X Z : Mat k d) :
    (mixedCubeAverage (centeredRho ν s) η X Z).toReal ≤
      (boxScale k η).toReal^2*2^(2*(d/16)) := by
  have hb := (mixedCube_le (centeredRho ν s) η X Z).trans
    (mul_le_mul_right (centered_rho_mass ν hν s) _)
  apply (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top (boxScale_ne_top k hη)) ENNReal.ofReal_ne_top) hb).trans_eq
  simp [ENNReal.toReal_mul,ENNReal.toReal_pow]

lemma mixedCube_finite {d k : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ u ∂ν,‖u‖=1) (s : Ambient d) {η : ℝ} (hη : 0 < η) (X Z : Mat k d) :
    mixedCubeAverage (centeredRho ν s) η X Z ≠ ∞ := by
  have := centered_finite ν hν s
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (boxScale_ne_top k hη)) (measure_ne_top _ _))
    (mixedCube_le (centeredRho ν s) η X Z)

lemma projected_log_bounded {d k : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ s ∂ν,‖s‖=1) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ z : Observation k d,
      0 ≤ Real.log (1+(projectedReference ν η z.1.1 z.1.2 z.2.1 z.2.2).toReal) ∧
      Real.log (1+(projectedReference ν η z.1.1 z.1.2 z.2.1 z.2.2).toReal) ≤ M := by
  refine ⟨Real.log (1+(boxScale k η).toReal^2*2^(2*(d/16))),Real.log_nonneg (by
      have hb : 0 ≤ (boxScale k η).toReal^2*2^(2*(d/16)) := by positivity
      linarith),?_⟩
  intro z
  exact ⟨Real.log_nonneg (by have := ENNReal.toReal_nonneg (a := projectedReference ν η z.1.1 z.1.2 z.2.1 z.2.2); linarith),
    Real.log_le_log (by positivity) (add_le_add_right (projectedReference_real_bound ν hν hη z) _)⟩

lemma mixed_log_bounded {d k : ℕ} (ν : Measure (Ambient d)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ u ∂ν,‖u‖=1) (s : Ambient d) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ X Z : Mat k d,
      0 ≤ Real.log (1+2^(2*k)*(mixedCubeAverage (centeredRho ν s) η X Z).toReal) ∧
      Real.log (1+2^(2*k)*(mixedCubeAverage (centeredRho ν s) η X Z).toReal) ≤ M := by
  have hB : 0 ≤ (2:ℝ)^(2*k)*((boxScale k η).toReal^2*2^(2*(d/16))) := by positivity
  refine ⟨Real.log (1+2^(2*k)*((boxScale k η).toReal^2*2^(2*(d/16)))),
    Real.log_nonneg (by linarith),?_⟩
  intro X Z
  constructor
  · apply Real.log_nonneg
    have : 0 ≤ (2:ℝ)^(2*k)*(mixedCubeAverage (centeredRho ν s) η X Z).toReal := by positivity
    linarith
  · exact Real.log_le_log (by positivity)
      (add_le_add_right (mul_le_mul_of_nonneg_left (mixedCube_real_bound ν hν s hη X Z) (by positivity : (0:ℝ) ≤ 2^(2*k))) _)

lemma noisy_weighted_projection {d : ℕ} (hd : 16 ≤ d)
    (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) (hs : ‖s‖=1)
    (L : ℕ) (hL : H*(9*3^d:ℝ) ≤ 2^L) {η : ℝ} (hη : 0 < η)
    (φ : ((Mat (d/16) d) × (Fin (d/16) → ℝ)) → ℝ) (hφ : Measurable φ)
    (hφ0 : ∀ t,0 ≤ φ t) (hφ1 : ∀ t,φ t ≤ 1) :
    (∫ z : Observation (d/16) d,φ (z.1.1,z.2.1)*
      Real.log (1+(projectedReference ν η z.1.1 z.1.2 z.2.1 z.2.2).toReal)
      ∂(observationBase (d/16) d).withDensity (fun z => observationKernel η z s)) ≤
      -(∫ X,∫ e,φ (X,projectVector X s+e) ∂noiseLaw (d/16) η ∂gaussianRows (d/16) d)*
        Real.log (∫ X,∫ e,φ (X,projectVector X s+e) ∂noiseLaw (d/16) η ∂gaussianRows (d/16) d)/(d/16:ℕ)+
      (∫ X,∫ e,φ (X,projectVector X s+e) ∂noiseLaw (d/16) η ∂gaussianRows (d/16) d)*
        (10*(d:ℝ)+Real.log ((L:ℝ)+2)) := by
  have hnorm := (Measure.absolutelyContinuous_of_le_smul hν).ae_le (ae_unit_norm (by omega : 0 < d))
  have := rho_finite ν hnorm
  have := centered_finite ν hnorm s
  have := sampling_probability (d/16) d hη
  have := noise_probability (d/16) hη
  have : IsProbabilityMeasure (gaussianRows (d/16) d) := by unfold gaussianRows; infer_instance
  let u : Mat (d/16) d → ℝ := fun X => ∫ e,φ (X,projectVector X s+e) ∂noiseLaw (d/16) η
  have hu := noiseAverage_measurable hη φ hφ s
  have hu0 (X) : 0 ≤ u X := integral_nonneg (fun _ => hφ0 _)
  have hu1 (X) : u X ≤ 1 := by
    have him : Measurable (fun e => φ (X,projectVector X s+e)) := by fun_prop
    have hi := Integrable.of_bound him.aestronglyMeasurable 1
      (ae_of_all (noiseLaw (d/16) η) (fun _ => by rw [Real.norm_eq_abs,abs_of_nonneg (hφ0 _)]; exact hφ1 _))
    simpa [u] using integral_mono hi (integrable_const 1) (fun _ => hφ1 _)
  let F : Mat (d/16) d × Mat (d/16) d → ℝ := fun XZ =>
    Real.log (1+2^(2*(d/16))*(mixedCubeAverage (centeredRho ν s) (2*η) XZ.1 XZ.2).toReal)
  have hF : Measurable F := by
    have hh := mixedCube_measurable (k := d/16) (centeredRho ν s) (2*η)
    exact (measurable_const.add (measurable_const.mul hh.ennreal_toReal)).log
  obtain ⟨M,_hM,hFb⟩ := mixed_log_bounded (k := d/16) ν hnorm s (by positivity : 0 < 2*η)
  obtain ⟨T,_hT,hPb⟩ := projected_log_bounded (k := d/16) ν hnorm hη
  let g : Observation (d/16) d → ℝ := fun t => φ ((sampleEquiv s t).1.1,(sampleEquiv s t).2.1)*
    Real.log (1+(projectedReference ν η (sampleEquiv s t).1.1 (sampleEquiv s t).1.2
      (sampleEquiv s t).2.1 (sampleEquiv s t).2.2).toReal)
  let f : Observation (d/16) d → ℝ := fun t => φ ((sampleEquiv s t).1.1,(sampleEquiv s t).2.1)*F t.1
  have hφs : Measurable (fun t : Observation (d/16) d => φ ((sampleEquiv s t).1.1,(sampleEquiv s t).2.1)) :=
    hφ.comp ((sampleEquiv s).measurable.fst.fst.prodMk (sampleEquiv s).measurable.snd.fst)
  have hg : Measurable g := by
    have hP := (projectedReference_measurable (k := d/16) ν η).comp (sampleEquiv s).measurable
    exact hφs.mul (measurable_const.add hP.ennreal_toReal).log
  have hf : Measurable f := hφs.mul (hF.comp measurable_fst)
  have hgb (t) : ‖g t‖ ≤ T := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hφ0 _) (hPb _).1)]
    exact (mul_le_mul_of_nonneg_right (hφ1 _) (hPb _).1).trans (by simpa using (hPb _).2)
  have hfb (t) : ‖f t‖ ≤ M := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hφ0 _) (hFb _ _).1)]
    exact (mul_le_mul_of_nonneg_right (hφ1 _) (hFb _ _).1).trans (by simpa using (hFb _ _).2)
  have hfg : (∫ t,g t ∂samplingLaw (d/16) d η) ≤ ∫ t,f t ∂samplingLaw (d/16) d η := by
    apply integral_mono_ae (Integrable.of_bound hg.aestronglyMeasurable T (ae_of_all _ hgb))
      (Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ hfb))
    filter_upwards [sampling_noise_mem (d := d) hη] with t ht
    apply mul_le_mul_of_nonneg_left _ (hφ0 _)
    apply Real.log_le_log (by positivity)
    apply add_le_add_right
    have hh := projectedReference_shift_le ν hη t.1.1 t.1.2 s t.2.1 t.2.2 ht.1 ht.2
    have hfin := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := (2:ℝ)^(2*(d/16))))
      (mixedCube_finite ν hnorm s (by positivity : 0 < 2*η) t.1.1 t.1.2)
    have hhR := ENNReal.toReal_mono hfin hh
    simpa only [sampleEquiv,MeasurableEquiv.coe_mk,Equiv.coe_fn_mk,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 2^(2*(d/16)))] using hhR
  rw [sample_integral hη s]
  change (∫ t,g t ∂samplingLaw (d/16) d η) ≤ _
  apply hfg.trans
  rw [sampling_integral_bounded hη f hf hfb]
  have he : (∫ X,∫ Z,∫ e,∫ e',f ((X,Z),(e,e')) ∂noiseLaw (d/16) η ∂noiseLaw (d/16) η
      ∂gaussianRows (d/16) d ∂gaussianRows (d/16) d)=
      ∫ X,u X*(∫ Z,F (X,Z) ∂gaussianRows (d/16) d) ∂gaussianRows (d/16) d := by
    simp only [f,sampleEquiv,MeasurableEquiv.coe_mk,Equiv.coe_fn_mk,integral_const,
      probReal_univ,one_smul,integral_mul_const,integral_const_mul,u]
  rw [he]
  exact weighted_centered_projection hd ν hH hν s hs L hL (by positivity : 0 < 2*η) u hu hu0 hu1
end KernelPotential.Noise

end OAI
