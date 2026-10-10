import OAI.Probability.PosteriorReplicas.Geometry.DensityBinsGeometry
import OAI.Probability.PosteriorReplicas.Geometry.LabelConvolution
import OAI.Probability.PosteriorReplicas.Measures.ReferenceMoments

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

def expectedDensity {d k m : ℕ} (f : Vec d → ℝ≥0∞) (u : Tuple d m) : ℝ≥0∞ :=
  ∫⁻ A, projectedDensity .spherical f (residualRows u A)
    (labels (residualRows u A) (u 0)) ∂gaussianRows d k

@[fun_prop] lemma measurable_expectedDensity {d k m : ℕ} {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) : Measurable (@expectedDensity d k m f) := by
  unfold expectedDensity
  fun_prop

def binEnvelope {d k : ℕ} (ν : Measure (Vec d)) (J : ℕ) (A : Rows d k) (y : Labels k) : ℝ≥0∞ :=
  2 + ∑ j ∈ Finset.range J, ENNReal.ofReal ((2:ℝ)^(k*(j+1))) * ellipsoidMass ν A y ((1/2:ℝ)^j)

@[fun_prop] lemma measurable_binEnvelope {d k : ℕ} (ν : Measure (Vec d)) [SFinite ν] (J : ℕ) :
    Measurable (fun z : Data d k => binEnvelope ν J z.1 z.2) := by
  unfold binEnvelope
  fun_prop

lemma ae_expectedDensity_le_inverse {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    ∀ᵐ u : Tuple d m ∂Measure.pi (fun _ => (sphereLaw d).withDensity f),
      expectedDensity (k := k) f u ≤ ∫⁻ x, ENNReal.ofReal ((tupleDistance u x)⁻¹^k)
        ∂(sphereLaw d).withDensity f := by
  let : NeZero d := ⟨by omega⟩
  have : IsProbabilityMeasure (sphereLaw d) := by
    change IsProbabilityMeasure (BaseLaw.spherical.measure d); infer_instance
  have := bounded_withDensity_finite (sphereLaw d) hLt hfL
  have h := (equalLabelVersions d k m hk hm (by omega) .spherical f hf ⟨L,hLt,hfL⟩).2.2.2.2
  filter_upwards [h] with u hu
  have hu' : LinearIndependent ℝ (differences u) := hu.1
  have he : (fun A : Rows d k => residualRows u A) =
      fun A i => (differenceSpan u)ᗮ.starProjection (A i) := by
    funext A i
    exact kernelComponent_eq_starProjection hu' _
  have hv : (fun A : Rows d k => projectedDensity .spherical f A (labels A (u 0))) =ᵐ[constrainedRows k u]
      (fun A => ballDensityVersion ((sphereLaw d).withDensity f) A (labels A (u 0))) := by
    filter_upwards [hu.2] with A hA
    exact hA.2.2.2.2.2.1
  rw [constrainedRows_eq_residualRows hu'] at hv
  have hv' := (ae_map_iff (show Measurable (residualRows u) by fun_prop).aemeasurable
    (measurableSet_eq_fun (by unfold labels; fun_prop) (by unfold labels; fun_prop))).mp hv
  unfold expectedDensity
  rw [lintegral_congr_ae hv']
  simp_rw [he]
  apply expected_ballDensityVersion_le _ _ _
  filter_upwards [tupleDistance_pos_ae (by omega) (by omega) u f] with x hx
  exact norm_ne_zero_iff.mp (ne_of_gt hx)

lemma ae_constrainedRows_mem {d k m : ℕ} (u : Tuple d m) :
    ∀ᵐ A ∂constrainedRows k u, ∀ i, A i ∈ (differenceSpan u)ᗮ := by
  unfold constrainedRows
  have hp : MeasurableSet {A : Rows d k | ∀ i, A i ∈ (differenceSpan u)ᗮ} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => (differenceSpan u)ᗮ.closed_of_finiteDimensional.measurableSet.preimage (measurable_pi_apply i))
  exact (ae_map_iff (show AEMeasurable (fun A : Rows d k => fun i =>
      (differenceSpan u)ᗮ.starProjection (A i)) _ from
        (Measurable.of_eval (fun i => (differenceSpan u)ᗮ.starProjection.continuous.measurable.comp (measurable_pi_apply i))).aemeasurable) hp).mpr
    (ae_of_all _ (fun A i => Submodule.starProjection_apply_mem _ _))

lemma ae_equalReference_bin_bound {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] (J : ℕ)
    (hcut : (L*ENNReal.ofReal ((72:ℝ)^d))*ENNReal.ofReal ((1/2:ℝ)^J)*
      (1+(2:ℝ≥0∞)^(k+1)) ≤ 1) :
    ∀ᵐ z : EqualSpace d k m ∂equalReference ((sphereLaw d).withDensity f),
      expectedDensity (k := k) f z.2.2 ≤ binEnvelope ((sphereLaw d).withDensity f) J z.1 z.2.1 := by
  apply ae_equalReference_of_constrained (by omega) (by omega) .spherical hf hLt hfL
    (measurableSet_le (by fun_prop) (by fun_prop))
  filter_upwards [ae_expectedDensity_le_inverse hd hk hm hf hLt hfL,
    ae_constrained_support hd hk hm .spherical hf hLt hfL] with u hu hs
  filter_upwards [hs.2, ae_constrainedRows_mem (k := k) u] with A hA hU
  exact hu.trans (density_inverse_moment_bins hd u hfL J hcut hA.1 hU)

lemma binTerm_volume {k : ℕ} (j : ℕ) :
    ENNReal.ofReal ((2:ℝ)^(k*(j+1))) * volume {y : Labels k | labelNorm y ≤ (1/2:ℝ)^j} =
      (2:ℝ≥0∞)^k * volume {y : Labels k | labelNorm y ≤ 1} := by
  rw [label_closedBall_scale (by positivity), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have he : (2:ℝ)^(k*(j+1)) * ((1/2:ℝ)^j)^k = (2:ℝ)^k := by
    rw [Nat.mul_comm k (j+1), pow_mul, ← mul_pow]
    congr 1
    rw [pow_succ, div_pow, one_pow, div_eq_mul_inv]
    field_simp
  rw [he, ENNReal.ofReal_pow (by norm_num)]
  norm_num

lemma normalized_binEnvelope_integral_le {d k : ℕ} {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)]
    {A : Rows d k} (hA : LinearIndependent ℝ A) (J : ℕ) :
    (∫⁻ y, (projectedDensity .spherical f A y)⁻¹ * binEnvelope ((sphereLaw d).withDensity f) J A y
      ∂volume.withDensity (projectedDensity .spherical f A)) ≤
      ENNReal.ofReal (gramVolume A) * volume {y : Labels k | labelNorm y ≤ 1} *
        (2+(J:ℝ≥0∞)*2^k) := by
  simp only [binEnvelope, mul_add, Finset.mul_sum]
  rw [lintegral_add_left (by fun_prop), lintegral_mul_const _ (by fun_prop),
    normalized_inverse_density_integral _ (by fun_prop) (projectedDensity_ne_top .spherical hLt hfL A),
    lintegral_finsetSum _ (fun j _ => by fun_prop)]
  calc
    _ ≤ (ENNReal.ofReal (gramVolume A) * volume {y : Labels k | labelNorm y ≤ 1}) * 2 +
        ∑ j ∈ Finset.range J, ENNReal.ofReal ((2:ℝ)^(k*(j+1))) *
          (ENNReal.ofReal (gramVolume A) * volume {y : Labels k | labelNorm y ≤ (1/2:ℝ)^j}) := by
      apply add_le_add
      · exact mul_le_mul' (projectedDensity_support_volume hA f) le_rfl
      · apply Finset.sum_le_sum
        intro j hj
        simp only [← Nat.mul_add]
        simp_rw [mul_left_comm ((projectedDensity .spherical f A _)⁻¹) (ENNReal.ofReal ((2:ℝ)^(k*(j+1))))]
        rw [lintegral_const_mul _ (by fun_prop)]
        exact mul_le_mul' le_rfl (normalized_ellipsoidMass_integral_le hf hLt hfL hA _)
    _ = _ := by
      simp_rw [mul_left_comm _ (ENNReal.ofReal (gramVolume A)), binTerm_volume]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

end PosteriorReplicas
end

end OAI
