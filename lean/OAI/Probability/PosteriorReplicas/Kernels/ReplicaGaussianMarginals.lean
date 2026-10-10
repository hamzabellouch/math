import OAI.Probability.PosteriorReplicas.Kernels.DensityRatio

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

def projectionGramRatio {d ℓ k m : ℕ} (z : EqualSpace d k m × AuxSpace d ℓ k) : ℝ :=
  gramVolume (pairingColumns (differences z.1.2.2) z.2.1) / affineVolume z.1.2.2

@[fun_prop] lemma measurable_projectionGramRatio {d ℓ k m : ℕ} :
    Measurable (@projectionGramRatio d ℓ k m) := by unfold projectionGramRatio; fun_prop

lemma projectionGramRatio_law {d ℓ k m : ℕ}
    (μ : Measure (EqualSpace d k m)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ z ∂μ, LinearIndependent ℝ (differences z.2.2)) :
    (μ.prod (auxLaw d ℓ k)).map projectionGramRatio = (gaussianRows ℓ m).map gramVolume := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by fun_prop),lintegral_map hf (by fun_prop),lintegral_prod _ (by fun_prop)]
  calc
    _ = ∫⁻ z, ∫⁻ G, f (gramVolume G) ∂gaussianRows ℓ m ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hμ] with z hz
      unfold projectionGramRatio
      rw [auxLaw,lintegral_prod _ (by fun_prop)]
      simp only [lintegral_const,measure_univ,mul_one]
      have he (B : Rows d ℓ) : gramVolume (pairingColumns (differences z.2.2) B) / affineVolume z.2.2 =
          gramVolume (pairingColumns (gramSchmidtNormed ℝ (differences z.2.2)) B) := by
        rw [gramVolume_pairingColumns hz]
        change gramVolume (differences z.2.2) * _ / gramVolume (differences z.2.2) = _
        field_simp [(gramVolume_pos hz).ne']
      simp_rw [he]
      have h := congrArg (fun ν : Measure (Rows ℓ m) => ∫⁻ G, f (gramVolume G) ∂ν)
        (orthonormal_pairingColumns_law (ℓ := ℓ) (gramSchmidtNormed_orthonormal hz))
      rw [lintegral_map (by fun_prop) (by fun_prop)] at h
      exact h
    _ = _ := by simp

lemma projectionGramRatio_log_integrable {d ℓ k m : ℕ} (hml : m+1 ≤ ℓ)
    (μ : Measure (EqualSpace d k m)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ z ∂μ, LinearIndependent ℝ (differences z.2.2)) :
    Integrable (fun z => Real.log (projectionGramRatio z)) (μ.prod (auxLaw d ℓ k)) := by
  have h : Integrable Real.log ((μ.prod (auxLaw d ℓ k)).map projectionGramRatio) := by
    rw [projectionGramRatio_law μ hμ]
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
    exact gaussian_integrable_log_gramVolume (by simpa using hml)
  exact h.comp_measurable (by fun_prop)

lemma projectionGramRatio_log_mean_le {d ℓ k m : ℕ} (hml : m+1 ≤ ℓ)
    (μ : Measure (EqualSpace d k m)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ z ∂μ, LinearIndependent ℝ (differences z.2.2)) :
    (∫ z, Real.log (projectionGramRatio z) ∂μ.prod (auxLaw d ℓ k)) ≤
      (m:ℝ)/2 * Real.log ((ℓ:ℝ)+1) := by
  rw [← integral_map (show Measurable (@projectionGramRatio d ℓ k m) by fun_prop).aemeasurable (by fun_prop),
    projectionGramRatio_law μ hμ,integral_map (by fun_prop) (by fun_prop)]
  simpa only [finrank_euclideanSpace_fin, gaussianRows] using
    (gaussian_integral_log_gramVolume_le (E := Vec ℓ) (m := m) (by simpa using hml))

lemma replicaLaw_sensing_law {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((base.measure d).withDensity f)] :
    (replicaLaw (k := k) (m := m) base f).map Prod.fst = gaussianRows d k := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH measurable_fst,replicaLaw_data_lintegral hd hk hm base hf hLt hfL
    (H := fun z => H z.1) (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [ae_gaussian_rows_full_rank (by omega : 3 ≤ d) (by omega : k < d)] with A hA
  rw [lintegral_const,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    lintegral_projectedDensity hA (by omega) base hf,measure_univ,mul_one]

lemma replicaLaw_sensing_log_integrable {d ℓ k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] :
    Integrable (fun z : EqualSpace d k m × AuxSpace d ℓ k => Real.log (gramVolume z.1.1))
      ((replicaLaw .spherical f).prod (auxLaw d ℓ k)) := by
  have : IsProbabilityMeasure ((BaseLaw.spherical.measure d).withDensity f) := by
    change IsProbabilityMeasure ((sphereLaw d).withDensity f); infer_instance
  have hmap : ((replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)).map (fun z => z.1.1) =
      gaussianRows d k := by
    change (((replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)).map (Prod.fst ∘ Prod.fst)) = _
    rw [← Measure.map_map measurable_fst measurable_fst,Measure.map_fst_prod,measure_univ,one_smul,
      replicaLaw_sensing_law hd hk hm .spherical hf hLt hfL]
  have h : Integrable (fun A : Rows d k => Real.log (gramVolume A))
      (((replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)).map (fun z => z.1.1)) := by
    rw [hmap]
    exact gaussian_integrable_log_gramVolume (by simp; omega)
  exact h.comp_measurable (by fun_prop)

lemma replicaLaw_sensing_log_mean_le {d ℓ k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] :
    (∫ z : EqualSpace d k m × AuxSpace d ℓ k, Real.log (gramVolume z.1.1)
      ∂((replicaLaw .spherical f).prod (auxLaw d ℓ k))) ≤ (k:ℝ)/2 * Real.log ((d:ℝ)+1) := by
  have : IsProbabilityMeasure ((BaseLaw.spherical.measure d).withDensity f) := by
    change IsProbabilityMeasure ((sphereLaw d).withDensity f); infer_instance
  have hmap : ((replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)).map (fun z => z.1.1) =
      gaussianRows d k := by
    change (((replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)).map (Prod.fst ∘ Prod.fst)) = _
    rw [← Measure.map_map measurable_fst measurable_fst,Measure.map_fst_prod,measure_univ,one_smul,
      replicaLaw_sensing_law hd hk hm .spherical hf hLt hfL]
  rw [← integral_map (show Measurable (fun z : EqualSpace d k m × AuxSpace d ℓ k => z.1.1) by fun_prop).aemeasurable
      measurable_gramVolume.log.aestronglyMeasurable, hmap]
  simpa only [finrank_euclideanSpace_fin, gaussianRows] using
    gaussian_integral_log_gramVolume_le (E := Vec d) (m := k) (by simp; omega)

end PosteriorReplicas
end

end OAI
