import OAI.Probability.PosteriorReplicas.Information.KLTools
import OAI.Probability.PosteriorReplicas.Information.NormalizedLikelihood
import OAI.Probability.PosteriorReplicas.Kernels.ReplicaGaussianMarginals

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma liftedReplica_absolutelyContinuous {d ℓ k m : ℕ} (f : Vec d → ℝ≥0∞) :
    ((replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)) ≪
      ((equalReference ((sphereLaw d).withDensity f)).prod (auxLaw d ℓ k)) :=
  (withDensity_absolutelyContinuous _ _).prod (Measure.AbsolutelyContinuous.refl _)

lemma liftedReplica_llr {d ℓ k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] :
    ∀ᵐ z ∂(replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k),
      llr ((replicaLaw .spherical f).prod (auxLaw d ℓ k))
        ((equalReference ((sphereLaw d).withDensity f)).prod (auxLaw d ℓ k)) z =
      Real.log (replicaDensity .spherical f z.1).toReal := by
  have : IsProbabilityMeasure ((BaseLaw.spherical.measure d).withDensity f) := by
    change IsProbabilityMeasure ((sphereLaw d).withDensity f); infer_instance
  have := replicaLaw_probability hd hk hm .spherical hf hLt hfL
  have he : ((replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)) =
      ((equalReference ((sphereLaw d).withDensity f)).prod (auxLaw d ℓ k)).withDensity
        (fun z => replicaDensity .spherical f z.1) := prod_withDensity_left (measurable_replicaDensity .spherical hf)
  have : IsFiniteMeasure (((equalReference ((sphereLaw d).withDensity f)).prod (auxLaw d ℓ k)).withDensity
      (fun z : EqualSpace d k m × AuxSpace d ℓ k => replicaDensity .spherical f z.1)) := by
    rw [← he]; infer_instance
  rw [he]
  exact llr_withDensity_ae _ (by fun_prop)

lemma replicaLaw_ae_sensing_full_rank {d k m : ℕ} (hd : k+m+2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] :
    ∀ᵐ z : EqualSpace d k m ∂replicaLaw .spherical f, LinearIndependent ℝ z.1 := by
  have : IsProbabilityMeasure ((BaseLaw.spherical.measure d).withDensity f) := by
    change IsProbabilityMeasure ((sphereLaw d).withDensity f); infer_instance
  have h := ae_gaussian_rows_full_rank (by omega : 3 ≤ d) (by omega : k < d)
  rw [← replicaLaw_sensing_law hd hk hm .spherical hf hLt hfL] at h
  exact (ae_map_iff measurable_fst.aemeasurable isOpen_setOfPred_linearIndependent.measurableSet).mp h

lemma liftedReplica_ae_observable_density_pos {d ℓ k m : ℕ} (hd : k+m+2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m ≤ ℓ)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] :
    ∀ᵐ z ∂(replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k),
      0 < projectedDensity .spherical f (observableRows z.1.2.2 z.2)
        (labels (observableRows z.1.2.2 z.2) (z.1.2.2 0)) := by
  apply (liftedReplica_absolutelyContinuous f).ae_le
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const (by unfold labels; fun_prop))).mpr
  have h : ∀ᵐ u : Tuple d m ∂(equalReference (k := k) ((sphereLaw d).withDensity f)).map (fun z => z.2.2),
      ∀ᵐ b ∂auxLaw d ℓ k, 0 < projectedDensity .spherical f (observableRows u b) (labels (observableRows u b) (u 0)) := by
    rw [equalReference_tuple]
    filter_upwards [ae_constrained_support hd hk hm .spherical hf hLt hfL] with u hu
    have hh : ∀ᵐ A ∂(auxLaw d ℓ k).map (observableRows u),
        0 < projectedDensity .spherical f A (labels A (u 0)) := by
      rw [observableRows_law hu.1 hkm]
      filter_upwards [hu.2] with A hA
      exact hA.2.2.2.1
    exact (ae_map_iff (show Measurable (observableRows u) by fun_prop).aemeasurable
      (measurableSet_lt measurable_const (by unfold labels; fun_prop))).mp hh
  exact ae_of_ae_map (show Measurable (fun z : EqualSpace d k m => z.2.2) by fun_prop).aemeasurable h

lemma liftedReplica_ae_projectionGram_pos {d ℓ k m : ℕ} (hd : 3 ≤ d) (hm : m < d) (hml : m < ℓ)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] :
    ∀ᵐ z ∂(replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k),
      0 < gramVolume (pairingColumns (differences z.1.2.2) z.2.1) := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const (by fun_prop))).mpr
  filter_upwards [replicaLaw_ae_tuple_full_rank hd hm hf hLt hfL] with z hz
  have hr : ∀ᵐ B ∂gaussianRows d ℓ, 0 < gramVolume (pairingColumns (differences z.2.2) B) := by
    have h := ae_pairingColumns_independent hz hml.le
    filter_upwards [h] with B hB
    exact gramVolume_pos hB
  exact Measure.quasiMeasurePreserving_fst.ae hr

end PosteriorReplicas
end

end OAI
