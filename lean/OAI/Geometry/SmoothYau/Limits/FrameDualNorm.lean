import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.NormalJetMapFirstPhase

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance frameDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance frameDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance frameFormNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance frameFormSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def metricFrameSet (g : SmoothMetric E E) (K : Set E) : Set (E × (E →L[ℝ] E)) :=
  {q | q.1 ∈ K ∧ ∀ v w : E, selfMetricFlat g q.1 (q.2 v) (q.2 w) = inner ℝ v w}

lemma metricFrameSet_fiber_nonempty (g : SmoothMetric E E) {K : Set E} {p : E}
    (hp : p ∈ K) : ∃ A : E →L[ℝ] E, (p,A) ∈ metricFrameSet g K := by
  obtain ⟨A,hA⟩ := exists_metric_orthonormal_frame g p
  exact ⟨A, hp, hA⟩

omit [FiniteDimensional ℝ E] in
lemma metricFrameSet_isClosed (g : SmoothMetric E E) {K : Set E} (hK : IsClosed K) :
    IsClosed (metricFrameSet g K) := by
  apply (hK.preimage continuous_fst).inter
  change IsClosed {q : E × (E →L[ℝ] E) | ∀ v w : E,
    selfMetricFlat g q.1 (q.2 v) (q.2 w) = inner ℝ v w}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro w
  exact isClosed_eq
    (((contDiff_selfMetricFlat g).continuous.comp continuous_fst).clm_apply
      (continuous_snd.clm_apply continuous_const) |>.clm_apply
      (continuous_snd.clm_apply continuous_const)) continuous_const

lemma metricFrameSet_bound (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ R > 0, ∀ q ∈ metricFrameSet g K, ‖q.2‖ ≤ R := by
  obtain ⟨m,hm,hml⟩ := compact_selfMetricFlat_lower g hK
  refine ⟨(Real.sqrt m)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hm), ?_⟩
  intro q hq
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  intro v
  have hlow := hml q.1 hq.1 (q.2 v)
  rw [hq.2 v v, real_inner_self_eq_norm_sq] at hlow
  have hh : Real.sqrt m * ‖q.2 v‖ ≤ ‖v‖ :=
    le_of_sq_le_sq (by simpa only [mul_pow,Real.sq_sqrt hm.le] using hlow) (norm_nonneg _)
  rw [← div_eq_inv_mul, le_div_iff₀ (Real.sqrt_pos.mpr hm)]
  rwa [mul_comm]

theorem metricFrameSet_isCompact (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    IsCompact (metricFrameSet g K) := by
  obtain ⟨R,hR,hb⟩ := metricFrameSet_bound g hK
  apply (hK.prod (isCompact_closedBall (0 : E →L[ℝ] E) R)).of_isClosed_subset
    (metricFrameSet_isClosed g hK.isClosed)
  intro q hq
  exact ⟨hq.1, by simpa only [Metric.mem_closedBall, dist_zero_right] using hb q hq⟩

omit [FiniteDimensional ℝ E] in
lemma metricFrameSet_injective (g : SmoothMetric E E) {K : Set E}
    {q : E × (E →L[ℝ] E)} (hq : q ∈ metricFrameSet g K) : Function.Injective q.2 := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change q.2 v = 0 at hv
  have h := hq.2 v v
  rw [hv, map_zero] at h
  exact inner_self_eq_zero.mp h.symm

lemma metricFrameSet_equiv (g : SmoothMetric E E) {K : Set E}
    {q : E × (E →L[ℝ] E)} (hq : q ∈ metricFrameSet g K) :
    ∃ A : E ≃L[ℝ] E, (A : E →L[ℝ] E) = q.2 := by
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective q.2.toLinearMap
    ((LinearMap.injective_iff_surjective).mp (metricFrameSet_injective g hq) |>
      fun hs => ⟨metricFrameSet_injective g hq,hs⟩)
  exact ⟨e.toContinuousLinearEquiv, rfl⟩

lemma metricFrameSet_inverse_continuousOn (g : SmoothMetric E E) {K : Set E} :
    ContinuousOn (fun q : E × (E →L[ℝ] E) => q.2.inverse) (metricFrameSet g K) := by
  intro q hq
  obtain ⟨A,hA⟩ := metricFrameSet_equiv g hq
  have h : q.2.IsInvertible := ⟨A,hA⟩
  exact (h.contDiffAt_map_inverse (n := (∞ : WithTop ℕ∞))).continuousAt.comp
    continuous_snd.continuousAt |>.continuousWithinAt

lemma metricFrameSet_inverse_bound (g : SmoothMetric E E) {K : Set E} (hK : IsCompact K) :
    ∃ R > 0, ∀ q ∈ metricFrameSet g K, ‖q.2.inverse‖ ≤ R := by
  obtain ⟨R,hR⟩ := (metricFrameSet_isCompact g hK).exists_bound_of_continuousOn
    (metricFrameSet_inverse_continuousOn g)
  refine ⟨max 1 R, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro q hq
  exact (hR q hq).trans (le_max_right _ _)
end YauCounterexamples
end

end OAI
