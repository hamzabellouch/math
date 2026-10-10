import Mathlib

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma local_diffeomorphism_det_ne_zero (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ ∞ e e.source) (he' : ContDiffOn ℝ ∞ e.symm e.target)
    {x : E} (hx : x ∈ e.source) : (fderiv ℝ e x).det ≠ 0 := by
  have hf := ((he x hx).contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)
  have hg := ((he' (e x) (e.map_source hx)).contDiffAt
    (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by simp)
  have hid : (fun y => e.symm (e y)) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have hder : (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x) = ContinuousLinearMap.id ℝ E := by
    apply HasFDerivAt.unique ((hg.hasFDerivAt.comp x hf.hasFDerivAt).congr_of_eventuallyEq hid.symm)
    exact hasFDerivAt_id x
  have hd := congrArg ContinuousLinearMap.det hder
  change LinearMap.det ((fderiv ℝ e.symm (e x)).toLinearMap.comp
    (fderiv ℝ e x).toLinearMap) = LinearMap.det (LinearMap.id : E →ₗ[ℝ] E) at hd
  rw [LinearMap.det_comp, LinearMap.det_id] at hd
  intro h
  simp only [h, mul_zero] at hd
  exact zero_ne_one hd

omit [FiniteDimensional ℝ E] in

lemma compact_jacobian_bound {K : Set E} (hK : IsCompact K) {φ : E → E}
    (hφ : ContDiff ℝ ∞ φ) (hn : ∀ x ∈ K, (fderiv ℝ φ x).det ≠ 0) :
    ∃ J : ℝ≥0, ∀ x ∈ K, 1 ≤ (J : ℝ≥0∞) * ENNReal.ofReal |(fderiv ℝ φ x).det| := by
  have hc : ContinuousOn (fun x => |(fderiv ℝ φ x).det|⁻¹) K := by
    apply ContinuousOn.inv₀
    · exact (ContinuousLinearMap.continuous_det.comp
        (hφ.continuous_fderiv (by simp))).abs.continuousOn
    · intro x hx
      simpa only [ne_eq, abs_eq_zero] using hn x hx
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨Real.toNNReal (|B| + 1), ?_⟩
  intro x hx
  have hpos : 0 < |(fderiv ℝ φ x).det| := abs_pos.mpr (hn x hx)
  have hh : |(fderiv ℝ φ x).det|⁻¹ ≤ |B| + 1 := by
    calc
      _ ≤ ‖|(fderiv ℝ φ x).det|⁻¹‖ := le_abs_self _
      _ ≤ B := hB x hx
      _ ≤ |B| + 1 := by linarith [le_abs_self B]
  have hr : 1 ≤ (|B| + 1) * |(fderiv ℝ φ x).det| := by
    have hm := mul_le_mul_of_nonneg_right hh hpos.le
    rwa [inv_mul_cancel₀ hpos.ne'] at hm
  rw [ENNReal.ofNNReal_toNNReal]
  have hh' := ENNReal.ofReal_le_ofReal hr
  simpa only [ENNReal.ofReal_one, ENNReal.ofReal_mul (by positivity : 0 ≤ |B| + 1)] using hh'

end YauCounterexamples

end

end OAI
