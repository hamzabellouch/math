import OAI.Geometry.CylinderCovering.Rational.CoordinateDictionary
import OAI.Geometry.CylinderCovering.Rational.Field
import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace RationalDictionary

theorem velocity_fderiv (d0 : ℝ) {p : Plane} (hs : p 1 + d0 ≠ 0) :
    fderiv ℝ (velocity d0) p =
      SlopeRational.matrixCLM
        ((1 + d0) * p 0 / (p 1 + d0) ^ 2)
        ((1 + d0) * (c0 ^ 2 * d0 ^ 2 - p 0 ^ 2) / (p 1 + d0) ^ 3)
        ((1 + d0) / (p 1 + d0))
        (-((1 + d0) * p 0) / (p 1 + d0) ^ 2) := by
  let u : Plane →L[ℝ] ℝ := EuclideanSpace.proj 0
  let s : Plane →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hu := u.hasFDerivAt (x := p)
  have ht := s.hasFDerivAt (x := p)
  have hr := ht.add_const d0
  have hs' : s p + d0 ≠ 0 := hs
  have hi := (hasDerivAt_inv hs').comp_hasFDerivAt p hr
  have hi₂ := (hasDerivAt_inv (pow_ne_zero 2 hs')).comp_hasFDerivAt p (hr.pow 2)
  have hg := hi.const_mul (1 + d0)
  have hgp := hi₂.const_mul (-(1 + d0))
  have hfirst := ((ht.const_mul (c0 ^ 2)).mul hg).add
    (((((ht.pow 2).const_mul (c0 ^ 2)).sub (hu.pow 2)).const_mul (1 / 2 : ℝ)).mul hgp)
  have hsecond := hu.mul hg
  have hf := (SlopeRational.hasFDerivAt_vec2 hfirst hsecond).fderiv
  change fderiv ℝ (velocity d0) p = _ at hf
  rw [hf]
  ext w i
  fin_cases i <;>
    simp [SlopeRational.matrixCLM, SlopeRational.vec2, u, s,
      ContinuousLinearMap.smulRight_apply] <;>
    field_simp [hs] <;> ring

theorem velocity_trace_det (d0 : ℝ) {p : Plane} (hs : p 1 + d0 ≠ 0) :
    LinearMap.trace ℝ Plane (fderiv ℝ (velocity d0) p).toLinearMap = 0 ∧
    LinearMap.det (fderiv ℝ (velocity d0) p).toLinearMap =
      -c0 ^ 2 * (((1 + d0) * d0) / (p 1 + d0) ^ 2) ^ 2 := by
  rw [velocity_fderiv d0 hs, SlopeRational.matrixCLM_trace,
    SlopeRational.matrixCLM_det]
  constructor
  · ring
  · field_simp
    ring

theorem velocity_det_neg {d0 : ℝ} (hd : 0 < d0) {p : Plane}
    (hs : p 1 + d0 ≠ 0) :
    LinearMap.det (fderiv ℝ (velocity d0) p).toLinearMap < 0 := by
  rw [(velocity_trace_det d0 hs).2]
  have hq : ((1 + d0) * d0) / (p 1 + d0) ^ 2 ≠ 0 := by
    apply div_ne_zero
    · exact mul_ne_zero (by linarith) hd.ne'
    · exact pow_ne_zero _ hs
  have hp := mul_pos (sq_pos_of_pos c0_pos) (sq_pos_of_ne_zero hq)
  nlinarith

theorem velocity_contDiffAt (d0 : ℝ) {p : Plane} (hs : p 1 + d0 ≠ 0) :
    ContDiffAt ℝ ∞ (velocity d0) p := by
  have hg : ContDiffAt ℝ ∞ (fun z : Plane => g d0 (z 1)) p := by
    unfold g
    exact ContDiffAt.div (by fun_prop) (by fun_prop) hs
  have hgp : ContDiffAt ℝ ∞ (fun z : Plane => gPrime d0 (z 1)) p := by
    unfold gPrime
    exact ContDiffAt.div (by fun_prop) (by fun_prop) (pow_ne_zero _ hs)
  apply contDiffAt_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun z : Plane => v1 d0 (z 0) (z 1)) p
    unfold v1
    fun_prop
  · change ContDiffAt ℝ ∞ (fun z : Plane => v2 d0 (z 0) (z 1)) p
    unfold v2
    fun_prop

theorem velocity_openRectangleC2 {d0 : ℝ} (hd : 0 < d0) (eta0 k : ℝ) :
    RuledApproximation.OpenRectangleC2 (uncenteredDomain d0 eta0 k) (velocity d0) := by
  refine ⟨vec2 (-2) (-d0 / 2), vec2 2 2, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · change (-2 : ℝ) < 2
      norm_num
    · change -d0 / 2 < 2
      linarith
  · intro p hp i
    have hc : c0 < 1 := by nlinarith [c0_sq, c0_pos]
    have hbound : |p 0| < 2 := by
      have := mul_le_mul_of_nonneg_left hp.2.1 c0_pos.le
      nlinarith [hp.2.2.1, c0_pos]
    fin_cases i
    · change -2 < p 0 ∧ p 0 < 2
      exact abs_lt.mp hbound
    · change -d0 / 2 < p 1 ∧ p 1 < 2
      exact ⟨by linarith [hp.1], by linarith [hp.2.1]⟩
  · intro p hp
    have hps := hp 1
    change -d0 / 2 < p 1 ∧ p 1 < 2 at hps
    have hs : p 1 + d0 ≠ 0 := by linarith [hps.1]
    exact ((velocity_contDiffAt d0 hs).of_le (by norm_cast)).contDiffWithinAt

theorem velocity_logarithmic_spectrum {d0 k : ℝ} (hd : 0 < d0)
    (hk : 0 < k) (hkd : k < d0 / (1 + d0)) {p : Plane} (hp : 0 ≤ p 1) :
    LinearMap.trace ℝ Plane (fderiv ℝ (velocity d0) p).toLinearMap = 0 ∧
    LinearMap.det (fderiv ℝ (velocity d0) p).toLinearMap < 0 ∧
    k * (2 * c0) * Real.sqrt (-LinearMap.det (fderiv ℝ (velocity d0) p).toLinearMap) < 1 := by
  have hspos : 0 < p 1 + d0 := add_pos_of_nonneg_of_pos hp hd
  have hs : p 1 + d0 ≠ 0 := hspos.ne'
  refine ⟨(velocity_trace_det d0 hs).1, velocity_det_neg hd hs, ?_⟩
  have hq : 0 ≤ ((1 + d0) * d0) / (p 1 + d0) ^ 2 := by positivity
  have hroot : Real.sqrt (-LinearMap.det (fderiv ℝ (velocity d0) p).toLinearMap) =
      c0 * (((1 + d0) * d0) / (p 1 + d0) ^ 2) := by
    rw [(velocity_trace_det d0 hs).2]
    rw [show -(-c0 ^ 2 * (((1 + d0) * d0) / (p 1 + d0) ^ 2) ^ 2) =
      (c0 * (((1 + d0) * d0) / (p 1 + d0) ^ 2)) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg c0_pos.le hq)
  rw [hroot]
  have he : k * (2 * c0) * (c0 * (((1 + d0) * d0) / (p 1 + d0) ^ 2)) =
      k * (1 + d0) * d0 / (p 1 + d0) ^ 2 := by
    calc
      _ = (2 * c0 ^ 2) * (k * (1 + d0) * d0 / (p 1 + d0) ^ 2) := by ring
      _ = _ := by rw [c0_sq]; ring
  rw [he]
  calc
    _ ≤ k * (1 + d0) * d0 / d0 ^ 2 :=
      div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg hk.le (by linarith)) hd.le) (sq_pos_of_pos hd)
        (by nlinarith [mul_nonneg hp hd.le, sq_nonneg (p 1)])
    _ < 1 := by
      apply (div_lt_one (sq_pos_of_pos hd)).mpr
      have hkm : k * (1 + d0) < d0 := (lt_div_iff₀ (by linarith)).mp hkd
      simpa only [pow_two] using mul_lt_mul_of_pos_right hkm hd

theorem uncenteredDomain_isClosed (d0 eta0 k : ℝ) :
    IsClosed (uncenteredDomain d0 eta0 k) := by
  have ht : Continuous (fun p : Plane => p 1) := by fun_prop
  have hu : Continuous (fun p : Plane => |p 0|) := by fun_prop
  have hw : Continuous (fun p : Plane => c0 * p 1) := by fun_prop
  have hc : Continuous (fun p : Plane => 1 + k ^ 2 * (a0 d0 (p 0) + eta0)) := by
    unfold a0
    fun_prop
  exact (isClosed_le continuous_const ht).inter
    ((isClosed_le ht continuous_const).inter ((isClosed_le hu hw).inter (isClosed_le ht hc)))

theorem uncenteredDomain_isCompact (d0 eta0 k : ℝ) :
    IsCompact (uncenteredDomain d0 eta0 k) := by
  apply (isCompact_closedBall (0 : Plane) 3).of_isClosed_subset
    (uncenteredDomain_isClosed d0 eta0 k)
  intro p hp
  have hc : c0 ≤ 1 := by nlinarith [c0_sq, c0_pos]
  have hpu : |p 0| ≤ 3 / 2 := by
    have := mul_le_mul_of_nonneg_left hp.2.1 c0_pos.le
    nlinarith [hp.2.2.1]
  have hps : |p 1| ≤ 3 / 2 := by rw [abs_of_nonneg hp.1]; exact hp.2.1
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (SlopeRational.plane_norm_le_sum p).trans (by linarith)

namespace UncenteredGeometry

def pairEquiv : (ℝ × ℝ) ≃ᵐ Plane :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

lemma pairEquiv_measurePreserving : MeasurePreserving pairEquiv volume volume :=
  (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_finTwoArrow ℝ).symm

lemma volume_graph_eq_zero {f : ℝ → ℝ} (hf : Continuous f) :
    volume {p : Plane | p 1 = f (p 0)} = 0 := by
  have hs : MeasurableSet {p : Plane | p 1 = f (p 0)} :=
    (isClosed_eq (by fun_prop) (hf.comp (by fun_prop))).measurableSet
  rw [← pairEquiv_measurePreserving.measure_preimage hs.nullMeasurableSet,
    Measure.volume_eq_prod]
  apply Measure.measure_prod_null_of_ae_null (hs.preimage pairEquiv.measurable)
  filter_upwards with u
  have heq : Prod.mk u ⁻¹' (pairEquiv ⁻¹' {p : Plane | p 1 = f (p 0)}) = {f u} := by
    ext t
    simp [pairEquiv, MeasurableEquiv.finTwoArrow]
  rw [heq]
  exact measure_singleton (f u)

end UncenteredGeometry

theorem frontier_uncenteredDomain_subset (d0 eta0 k : ℝ) :
    frontier (uncenteredDomain d0 eta0 k) ⊆
      {p : Plane | p 1 = 0} ∪ ({p : Plane | p 1 = 3 / 2} ∪
        ({p : Plane | p 1 = |p 0| / c0} ∪
          {p : Plane | p 1 = 1 + k ^ 2 * (a0 d0 (p 0) + eta0)})) := by
  intro p hp
  change p ∈ frontier ({z : Plane | 0 ≤ z 1} ∩
    ({z : Plane | z 1 ≤ 3 / 2} ∩
      ({z : Plane | |z 0| ≤ c0 * z 1} ∩
        {z : Plane | z 1 ≤ 1 + k ^ 2 * (a0 d0 (z 0) + eta0)}))) at hp
  rcases frontier_inter_subset _ _ hp with h0 | hr
  · left
    exact (frontier_le_subset_eq (f := fun _ : Plane => (0 : ℝ))
      (g := fun z => z 1) (by fun_prop) (by fun_prop) h0.1).symm
  · right
    rcases frontier_inter_subset _ _ hr.2 with htop | hw
    · left
      exact frontier_le_subset_eq (f := fun z : Plane => z 1)
        (g := fun _ => (3 / 2 : ℝ)) (by fun_prop) (by fun_prop) htop.1
    · right
      rcases frontier_inter_subset _ _ hw.2 with hwall | hcap
      · left
        have he := frontier_le_subset_eq (f := fun z : Plane => |z 0|)
          (g := fun z => c0 * z 1) (by fun_prop) (by fun_prop) hwall.1
        change p 1 = |p 0| / c0
        apply (eq_div_iff c0_pos.ne').mpr
        simpa only [mul_comm] using he.symm
      · right
        exact frontier_le_subset_eq (f := fun z : Plane => z 1)
          (g := fun z => 1 + k ^ 2 * (a0 d0 (z 0) + eta0))
          (by fun_prop) (by unfold a0; fun_prop) hcap.2

theorem volume_frontier_uncenteredDomain (d0 eta0 k : ℝ) :
    volume (frontier (uncenteredDomain d0 eta0 k)) = 0 := by
  apply measure_mono_null (frontier_uncenteredDomain_subset d0 eta0 k)
  apply measure_union_null
  · exact UncenteredGeometry.volume_graph_eq_zero continuous_const
  · apply measure_union_null
    · exact UncenteredGeometry.volume_graph_eq_zero continuous_const
    · apply measure_union_null
      · exact UncenteredGeometry.volume_graph_eq_zero (f := fun u => |u| / c0) (by fun_prop)
      · exact UncenteredGeometry.volume_graph_eq_zero
          (f := fun u => 1 + k ^ 2 * (a0 d0 u + eta0)) (by unfold a0; fun_prop)

end RationalDictionary

end

end OAI
