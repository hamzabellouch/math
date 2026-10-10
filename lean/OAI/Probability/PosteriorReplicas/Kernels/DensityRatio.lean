import OAI.Probability.PosteriorReplicas.Geometry.DensityBinEnvelope
import OAI.Probability.PosteriorReplicas.Information.ObservableLikelihood
import OAI.Probability.PosteriorReplicas.Kernels.PosteriorKernel

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

def normalizedRatio {d ℓ k m : ℕ} (f : Vec d → ℝ≥0∞)
    (z : EqualSpace d k m × AuxSpace d ℓ k) : ℝ≥0∞ :=
  (projectedDensity .spherical f (observableRows z.1.2.2 z.2)
    (labels (observableRows z.1.2.2 z.2) (z.1.2.2 0))) *
      (projectedDensity .spherical f z.1.1 z.1.2.1)⁻¹ * (ENNReal.ofReal (gramVolume z.1.1))⁻¹

@[fun_prop] lemma measurable_normalizedRatio {d ℓ k m : ℕ} {f : Vec d → ℝ≥0∞} (hf : Measurable f) :
    Measurable (@normalizedRatio d ℓ k m f) := by unfold normalizedRatio labels; fun_prop

lemma replicaLaw_ae_of_reference {d k m : ℕ} (base : BaseLaw) (f : Vec d → ℝ≥0∞)
    {P : EqualSpace d k m → Prop} (h : ∀ᵐ z ∂equalReference ((base.measure d).withDensity f), P z) :
    ∀ᵐ z ∂replicaLaw base f, P z :=
  (withDensity_absolutelyContinuous _ _).ae_le h

lemma replicaLaw_ae_tuple_full_rank {d k m : ℕ} (hd : 3 ≤ d) (hm : m < d)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] :
    ∀ᵐ z : EqualSpace d k m ∂replicaLaw .spherical f, LinearIndependent ℝ (differences z.2.2) := by
  apply replicaLaw_ae_of_reference
  have h : ∀ᵐ u : Tuple d m ∂(equalReference (k := k) ((sphereLaw d).withDensity f)).map (fun z => z.2.2),
      LinearIndependent ℝ (differences u) := by
    rw [equalReference_tuple]
    exact ae_tilt_tuple_full_rank hd hm .spherical hf hLt hfL
  exact (ae_map_iff (show Measurable (fun z : EqualSpace d k m => z.2.2) by fun_prop).aemeasurable
    (show MeasurableSet {u : Tuple d m | LinearIndependent ℝ (differences u)} from
      isOpen_setOfPred_linearIndependent.measurableSet.preimage (show Measurable (@differences d m) by fun_prop))).mp h

lemma replicaLaw_data_lintegral {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {H : Data d k → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ z : EqualSpace d k m, H (z.1,z.2.1) ∂replicaLaw base f) =
      ∫⁻ A, ∫⁻ y, H (A,y) ∂volume.withDensity (projectedDensity base f A) ∂gaussianRows d k := by
  have (A : Rows d k) (y : Labels k) := tiltedFiber_probability base hLt hfL A y
  rw [replicaLaw_lintegral hd hk hm base hf hLt hfL (by fun_prop)]
  simp only [lintegral_const,measure_univ,mul_one]
  apply lintegral_congr
  intro A
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  rfl

lemma normalizedRatio_lintegral_le {d ℓ k m : ℕ} (hd : k+m+2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m ≤ ℓ)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] (J : ℕ)
    (hcut : (L*ENNReal.ofReal ((72:ℝ)^d))*ENNReal.ofReal ((1/2:ℝ)^J)*
      (1+(2:ℝ≥0∞)^(k+1)) ≤ 1) :
    (∫⁻ z, normalizedRatio f z ∂(replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)) ≤
      volume {y : Labels k | labelNorm y ≤ 1} * (2+(J:ℝ≥0∞)*2^k) := by
  have : IsProbabilityMeasure ((BaseLaw.spherical.measure d).withDensity f) := by
    change IsProbabilityMeasure ((sphereLaw d).withDensity f); infer_instance
  have := replicaLaw_probability hd hk hm .spherical hf hLt hfL
  rw [lintegral_prod _ (by fun_prop)]
  calc
    _ ≤ ∫⁻ z : EqualSpace d k m,
        (projectedDensity .spherical f z.1 z.2.1)⁻¹ *
          binEnvelope ((sphereLaw d).withDensity f) J z.1 z.2.1 *
          (ENNReal.ofReal (gramVolume z.1))⁻¹ ∂replicaLaw .spherical f := by
      apply lintegral_mono_ae
      filter_upwards [replicaLaw_ae_of_reference .spherical f
        (ae_equalReference_bin_bound hd hk hm hf hLt hfL J hcut),replicaLaw_ae_tuple_full_rank (k := k) (by omega) (by omega) hf hLt hfL] with z hz hu
      unfold normalizedRatio
      dsimp only
      rw [lintegral_mul_const _ (by fun_prop),lintegral_mul_const _ (by unfold labels; fun_prop),
        observableDensity_expected hu hkm hf]
      change expectedDensity f z.2.2 * _ * _ ≤ _
      exact mul_le_mul' (by simpa only [mul_comm] using mul_le_mul' hz (le_refl (projectedDensity .spherical f z.1 z.2.1)⁻¹)) le_rfl
    _ = ∫⁻ A, (∫⁻ y, (projectedDensity .spherical f A y)⁻¹ *
        binEnvelope ((sphereLaw d).withDensity f) J A y
        ∂volume.withDensity (projectedDensity .spherical f A)) *
        (ENNReal.ofReal (gramVolume A))⁻¹ ∂gaussianRows d k := by
      rw [replicaLaw_data_lintegral hd hk hm .spherical hf hLt hfL
        (H := fun z => (projectedDensity .spherical f z.1 z.2)⁻¹ *
          binEnvelope ((sphereLaw d).withDensity f) J z.1 z.2 * (ENNReal.ofReal (gramVolume z.1))⁻¹) (by fun_prop)]
      apply lintegral_congr
      intro A
      exact lintegral_mul_const (μ := volume.withDensity (projectedDensity .spherical f A))
        (ENNReal.ofReal (gramVolume A))⁻¹ (show Measurable (fun y : Labels k => (projectedDensity .spherical f A y)⁻¹ *
        binEnvelope ((sphereLaw d).withDensity f) J A y) by fun_prop)
    _ ≤ ∫⁻ _A : Rows d k, volume {y : Labels k | labelNorm y ≤ 1} * (2+(J:ℝ≥0∞)*2^k)
        ∂gaussianRows d k := by
      apply lintegral_mono_ae
      filter_upwards [ae_gaussian_rows_full_rank (by omega : 3 ≤ d) (by omega : k < d)] with A hA
      apply (mul_le_mul' (normalized_binEnvelope_integral_le hf hLt hfL hA J) le_rfl).trans_eq
      have hp := ENNReal.ofReal_pos.mpr (gramVolume_pos hA)
      calc
        _ = (ENNReal.ofReal (gramVolume A) * (ENNReal.ofReal (gramVolume A))⁻¹) *
            (volume {y : Labels k | labelNorm y ≤ 1} * (2+(J:ℝ≥0∞)*2^k)) := by ring
        _ = _ := by rw [ENNReal.mul_inv_cancel hp.ne' ENNReal.ofReal_ne_top,one_mul]
    _ = _ := by simp

end PosteriorReplicas
end

end OAI
