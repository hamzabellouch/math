import OAI.Probability.PosteriorReplicas.Measures.ReferenceMoments

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma replicaDensity_ne_top_ae {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    ∀ᵐ z ∂equalReference (k := k) (m := m) ((base.measure d).withDensity f),
      replicaDensity base f z ≠ ∞ := by
  filter_upwards [ae_equalReference_density_pos hd hk hm base hf hLt hfL,
    ae_equalReference_affine_pos (by omega) (by omega) base hf hLt hfL] with z ha hw
  unfold replicaDensity equalConstant
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top (by finiteness)
    exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hw).ne')
  · exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr ha.ne')

lemma replica_log_integrable {d k m : ℕ} (hd : 4*k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] :
    Integrable (fun z : EqualSpace d k m => Real.log (replicaDensity .spherical f z).toReal)
      (replicaLaw .spherical f) := by
  have : IsProbabilityMeasure ((BaseLaw.spherical.measure d).withDensity f) := by
    change IsProbabilityMeasure ((sphereLaw d).withDensity f); infer_instance
  have hd' : k+m+2 ≤ d := by omega
  have := replicaLaw_probability hd' hk hm .spherical hf hLt hfL
  let R : Measure (EqualSpace d k m) := equalReference ((sphereLaw d).withDensity f)
  let w : EqualSpace d k m → ℝ≥0∞ := fun z => equalConstant k m * (ENNReal.ofReal (affineVolume z.2.2))⁻¹^k
  let a : EqualSpace d k m → ℝ≥0∞ := fun z => projectedDensity .spherical f z.1 z.2.1
  have hw : Measurable w := by unfold w; fun_prop
  have ha : Measurable a := by unfold a; fun_prop
  have he : R.withDensity (fun z => ENNReal.ofReal ((w z).toReal * (a z).toReal⁻¹^m)) =
      replicaLaw .spherical f := by
    apply withDensity_congr_ae
    filter_upwards [replicaDensity_ne_top_ae hd' hk hm .spherical hf hLt hfL] with z hz
    rw [← ENNReal.toReal_inv, ← ENNReal.toReal_pow, ← ENNReal.toReal_mul]
    exact ENNReal.ofReal_toReal hz
  have : IsFiniteMeasure (R.withDensity (fun z => ENNReal.ofReal ((w z).toReal * (a z).toReal⁻¹^m))) := by
    rw [he]; infer_instance
  have hw4 : Integrable (fun z => (w z).toReal^4) R := by
    have h := reference_weight_moment (n := 4) (by omega : k*4+m+2 ≤ d) hm .spherical hf hLt hfL
    simpa only [ENNReal.toReal_pow, BaseLaw.measure, R] using
      (integrable_toReal_of_lintegral_ne_top (hw.pow_const 4).aemeasurable h.ne)
  have hwa : Integrable (fun z => (w z).toReal * (a z).toReal⁻¹^(m+1)) R := by
    have h := reference_inverse_density_moment hd' hk hm .spherical hf hLt hfL
    have ht : (∫⁻ z, w z * (a z)⁻¹^(m+1) ∂ R) < ∞ := by
      exact lt_of_eq_of_lt (by simpa only [R,w,a,BaseLaw.measure] using h)
        (gaussian_label_support_volume_finite (by omega) (by omega) hf)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv] using
      (integrable_toReal_of_lintegral_ne_top (show AEMeasurable (fun z => w z * (a z)⁻¹^(m+1)) R by fun_prop) ht.ne)
  have hap : ∀ᵐ z ∂ R, 0 < (a z).toReal := by
    filter_upwards [ae_equalReference_density_pos hd' hk hm .spherical hf hLt hfL] with z hz
    exact ENNReal.toReal_pos hz.ne' (projectedDensity_ne_top .spherical hLt hfL z.1 z.2.1)
  have hi := replica_likelihood_integrable R hw.ennreal_toReal ha.ennreal_toReal
    (ae_of_all _ (fun z => ENNReal.toReal_nonneg)) hap m hw4 hwa
  rw [he] at hi
  simpa only [replicaDensity, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, w, a] using hi

lemma replica_klDiv_ne_top {d k m : ℕ} (hd : 4*k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] :
    klDiv (replicaLaw (k := k) (m := m) .spherical f)
      (equalReference ((sphereLaw d).withDensity f)) ≠ ∞ := by
  have : IsProbabilityMeasure ((BaseLaw.spherical.measure d).withDensity f) := by
    change IsProbabilityMeasure ((sphereLaw d).withDensity f); infer_instance
  have := replicaLaw_probability (by omega : k+m+2 ≤ d) hk hm .spherical hf hLt hfL
  apply klDiv_ne_top_iff.mpr
  refine ⟨withDensity_absolutelyContinuous _ _, ?_⟩
  have : IsFiniteMeasure
      ((equalReference ((BaseLaw.spherical.measure d).withDensity f)).withDensity
        (@replicaDensity d k m .spherical f)) := by
    change IsFiniteMeasure (replicaLaw (k := k) (m := m) .spherical f); infer_instance
  exact (replica_log_integrable hd hk hm hf hLt hfL).congr
    (llr_withDensity_ae _ (measurable_replicaDensity .spherical hf)).symm

end PosteriorReplicas
end

end OAI
