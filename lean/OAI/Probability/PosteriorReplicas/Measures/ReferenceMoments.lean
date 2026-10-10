import OAI.Probability.PosteriorReplicas.Geometry.LabelEllipsoids
import OAI.Probability.PosteriorReplicas.Information.LikelihoodIntegrability
import OAI.Probability.PosteriorReplicas.Kernels.ReplicaMeasure

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma tilt_tuple_inverse_finite {d k m : ℕ} (hd : k+m+2 ≤ d) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    (∫⁻ u : Tuple d m, (ENNReal.ofReal (affineVolume u))⁻¹^k
      ∂Measure.pi (fun _ => (base.measure d).withDensity f)) < ∞ := by
  let : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hLt hfL
  rw [pi_withDensity _ _ (fun _ => hf),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have hbound (u : Tuple d m) : (∏ i, f (u i)) ≤ L^(m+1) := by
    simpa using Finset.prod_le_prod (fun i (_ : i ∈ (Finset.univ : Finset (Fin (m+1)))) => hfL (u i))
  simp only [Pi.mul_apply]
  apply lt_of_le_of_lt (lintegral_mono (fun u => mul_le_mul' (hbound u) le_rfl))
  rw [lintegral_const_mul _ (by fun_prop)]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top hLt.lt_top) (base_tuple_inverse_finite hd hm base)

lemma ae_equalReference_of_constrained {d k m : ℕ} (hd : 3 ≤ d) (hm : m < d)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {P : EqualSpace d k m → Prop} (hP : MeasurableSet {z | P z})
    (h : ∀ᵐ u : Tuple d m ∂Measure.pi (fun _ => (base.measure d).withDensity f),
      ∀ᵐ A ∂constrainedRows k u, P (A,labels A (u 0),u)) :
    ∀ᵐ z ∂equalReference (k := k) (m := m) ((base.measure d).withDensity f), P z := by
  let : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hLt hfL
  unfold equalReference
  apply (ae_map_iff measurable_rightBasePoint.aemeasurable hP).mpr
  apply (Measure.ae_prod_iff_ae_ae (hP.preimage measurable_rightBasePoint)).mpr
  filter_upwards [h, ae_tilt_tuple_full_rank hd hm base hf hLt hfL] with u hu hU
  rw [constrainedRows_eq_residualRows hU] at hu
  exact (ae_map_iff (show Measurable (residualRows u) by fun_prop).aemeasurable
    (hP.preimage (show Measurable (fun A => (A,labels A (u 0),u)) by unfold labels; fun_prop))).mp hu

lemma ae_equalReference_density_pos {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    ∀ᵐ z ∂equalReference (k := k) (m := m) ((base.measure d).withDensity f),
      0 < projectedDensity base f z.1 z.2.1 := by
  apply ae_equalReference_of_constrained (by omega) (by omega) base hf hLt hfL
    (measurableSet_lt measurable_const (by fun_prop))
  filter_upwards [ae_constrained_support hd hk hm base hf hLt hfL] with u hu
  filter_upwards [hu.2] with A hA
  exact hA.2.2.2.1

lemma ae_equalReference_affine_pos {d k m : ℕ} (hd : 3 ≤ d) (hm : m < d)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    ∀ᵐ z ∂equalReference (k := k) (m := m) ((base.measure d).withDensity f),
      0 < affineVolume z.2.2 := by
  apply ae_equalReference_of_constrained hd hm base hf hLt hfL
    (measurableSet_lt measurable_const (by fun_prop))
  filter_upwards [ae_tilt_tuple_full_rank hd hm base hf hLt hfL] with u hu
  apply ae_of_all
  intro A
  exact Real.sqrt_pos.mpr (Matrix.posDef_gram_of_linearIndependent hu).det_pos

lemma reference_weight_moment {d k m n : ℕ} (hd : k*n+m+2 ≤ d) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    (∫⁻ z : EqualSpace d k m,
      (equalConstant k m * (ENNReal.ofReal (affineVolume z.2.2))⁻¹^k)^n
      ∂equalReference ((base.measure d).withDensity f)) < ∞ := by
  let : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hLt hfL
  rw [equalReference_lintegral _ (by fun_prop)]
  simp only [lintegral_const, measure_univ, mul_one, mul_pow, ← pow_mul]
  rw [lintegral_const_mul _ (by fun_prop)]
  exact ENNReal.mul_lt_top (by unfold equalConstant; finiteness)
    (tilt_tuple_inverse_finite hd hm base hf hLt hfL)

lemma reference_inverse_density_moment {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    (∫⁻ z : EqualSpace d k m,
      (equalConstant k m * (ENNReal.ofReal (affineVolume z.2.2))⁻¹^k) *
        (projectedDensity base f z.1 z.2.1)⁻¹^(m+1)
      ∂equalReference ((base.measure d).withDensity f)) =
      ∫⁻ A, (volume : Measure (Labels k)) {y | projectedDensity base f A y ≠ 0} ∂gaussianRows d k := by
  let : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hLt hfL
  have (A : Rows d k) (y : Labels k) := tiltedFiber_probability base hLt hfL A y
  have he := equal_label_tilt_identity hd hk hm base hf hLt hfL
    (H := fun z : EqualSpace d k m => (projectedDensity base f z.1 z.2.1)⁻¹^(m+1)) (by fun_prop)
  have hr : (∫⁻ z : EqualSpace d k m,
      (equalConstant k m * (ENNReal.ofReal (affineVolume z.2.2))⁻¹^k) *
        (projectedDensity base f z.1 z.2.1)⁻¹^(m+1)
      ∂equalReference ((base.measure d).withDensity f)) =
      equalLabelRight base f (fun z : EqualSpace d k m =>
        (projectedDensity base f z.1 z.2.1)⁻¹^(m+1)) := by
    rw [equalLabelRight_residual (by omega) (by omega) base hf hLt hfL (by fun_prop),
      equalReference_lintegral _ (by fun_prop)]
    rw [← lintegral_const_mul _ (show Measurable (fun u : Tuple d m =>
      (ENNReal.ofReal (affineVolume u))⁻¹^k * ∫⁻ A, (projectedDensity base f
        (residualRows u A) (labels (residualRows u A) (u 0)))⁻¹^(m+1) ∂gaussianRows d k) by
          unfold residualRows; fun_prop)]
    apply lintegral_congr
    intro u
    dsimp only [Prod.fst, Prod.snd]
    rw [lintegral_const_mul _ (show Measurable (fun A : Rows d k =>
      (projectedDensity base f (residualRows u A) (labels (residualRows u A) (u 0)))⁻¹^(m+1)) by
        unfold residualRows; fun_prop)]
    rw [mul_assoc]
  rw [hr, ← he]
  unfold equalLabelLeft
  apply lintegral_congr
  intro A
  simp only [lintegral_const, measure_univ, mul_one]
  rw [← lintegral_indicator_one (show MeasurableSet {y | projectedDensity base f A y ≠ 0} by
    exact (measurableSet_eq_fun (by fun_prop) measurable_const).compl)]
  apply lintegral_congr
  intro y
  by_cases ha : projectedDensity base f A y = 0
  · simp [ha]
  · rw [Set.indicator_of_mem (show y ∈ {y | projectedDensity base f A y ≠ 0} from ha)]
    rw [← mul_pow, ENNReal.mul_inv_cancel ha (projectedDensity_ne_top base hLt hfL A y), one_pow]
    rfl

end PosteriorReplicas
end

end OAI
