import OAI.Analysis.FiniteFactor.BoundedMatrixOperator
import Mathlib.Topology.MetricSpace.UniformConvergence

namespace OAI

namespace FiniteFactor
open Filter
open scoped Topology
noncomputable section

/-- A uniformly bounded field is strongly continuous wherever all its basis
columns are continuous. No norm-continuity of the field is required. -/
theorem fiberField_continuousOn {X : Type*} [TopologicalSpace X]
    (A : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (Q : Set X)
    (C : ℝ) (hC : ∀ x ∈ Q, ‖A x‖ ≤ C)
    (hb : ∀ k : ℤ, ContinuousOn (fun x => A x (lp.single 2 k (1 : ℂ))) Q)
    (v : SourceFiberHilbert) : ContinuousOn (fun x => A x v) Q := by
  classical
  let w : Finset ℤ → SourceFiberHilbert := fun s => ∑ k ∈ s, lp.single 2 k (v k)
  have hw : Tendsto w atTop (𝓝 v) := lp.hasSum_single (by norm_num) v
  have he : Tendsto (fun s => C * ‖v - w s‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := v)).sub hw).norm.const_mul C
  have hu : TendstoUniformlyOn (fun s x => A x (w s)) (fun x => A x v) atTop Q := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp he).2 ε hε] with s hs x hx
    rw [dist_eq_norm, ← map_sub]
    exact ((A x).le_opNorm (v - w s)).trans_lt
      ((mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _)).trans_lt hs)
  apply hu.continuousOn
  apply Filter.Eventually.frequently
  apply Eventually.of_forall
  intro s
  have hh : (fun x => A x (w s)) =
      fun x => ∑ k ∈ s, (v k) • A x (lp.single 2 k (1 : ℂ)) := by
    funext x
    simp only [w, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [show lp.single 2 k (v k) = (v k) • (lp.single 2 k (1 : ℂ) : SourceFiberHilbert) by
      simp [← lp.single_smul], map_smul]
  rw [hh]
  exact continuousOn_finsetSum s (fun k _ => (hb k).const_smul (v k))

/-- Evaluation on a varying continuous vector preserves strong continuity
under a uniform operator bound. -/
theorem fiberField_continuousOn_apply {X : Type*} [TopologicalSpace X]
    (A : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (Q : Set X)
    (C : ℝ) (hC : ∀ x ∈ Q, ‖A x‖ ≤ C)
    (hA : ∀ v, ContinuousOn (fun x => A x v) Q)
    (v : X → SourceFiberHilbert) (hv : ContinuousOn v Q) :
    ContinuousOn (fun x => A x (v x)) Q := by
  intro x hx
  have he : Tendsto (fun y => C * ‖v y - v x‖) (𝓝[Q] x) (𝓝 0) := by
    simpa using ((hv x hx).sub_const (v x)).norm.const_mul C
  have hzero : Tendsto (fun y => A y (v y - v x)) (𝓝[Q] x) (𝓝 0) := by
    apply squeeze_zero_norm' _ he
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ((A y).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hC y hy) (norm_nonneg _))
  have ht := hzero.add (hA (v x) x hx)
  change Tendsto _ _ _
  simpa only [map_sub, sub_add_cancel, zero_add] using ht

end
end FiniteFactor

end OAI
