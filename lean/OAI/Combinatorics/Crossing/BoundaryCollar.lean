import OAI.Combinatorics.Crossing.RadialExterior
import Mathlib.Analysis.Normed.Module.Convex

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem exists_radial_tip_collar (z x : Plane) (r : ℝ) (hr : 0 < r)
    (hx : squaredLength (x-z)=r^2) (U : Set Plane) (hU : IsOpen U) (hxu : x ∈ U) :
    ∃ α ρ : ℝ, 0 < α ∧ 0 < ρ ∧
      segment ℝ x (x+α • (x-z)) ⊆ U ∩ insert x {y | r^2 < squaredLength (y-z)} ∧
      (∀ y, dist y x < ρ → r^2 < squaredLength (y-z) →
        segment ℝ (x+α • (x-z)) y ⊆ U ∩ {p | r^2 < squaredLength (p-z)}) := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU x hxu
  have hmove : Continuous (fun α : ℝ => x+α • (x-z)) := by fun_prop
  have hevent : ∀ᶠ α : ℝ in 𝓝 0, x+α • (x-z) ∈ Metric.ball x ε :=
    hmove.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds x hε)
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp hevent
  let α := δ/2
  have hα : 0 < α := by dsimp [α]; positivity
  have htip : x+α • (x-z) ∈ Metric.ball x ε := hd (by
    rw [Real.dist_eq,sub_zero,abs_of_pos hα]
    dsimp [α]
    linarith)
  have hdpos : 0 < dot2 (x-z) ((x+α • (x-z))-x) := by
    rw [radial_tip_dot,hx]
    exact mul_pos hα (sq_pos_of_pos hr)
  have hdot : Continuous (fun y : Plane => dot2 (y-z) ((x+α • (x-z))-y)) := by
    unfold dot2
    fun_prop
  have hev : ∀ᶠ y : Plane in 𝓝 x, 0 < dot2 (y-z) ((x+α • (x-z))-y) :=
    continuousAt_const.eventually_lt hdot.continuousAt hdpos
  obtain ⟨σ,hσ,hσdot⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨α,min ε σ,hα,lt_min hε hσ,?_,?_⟩
  · apply Set.subset_inter
    · exact ((convex_ball x ε).segment_subset (Metric.mem_ball_self hε) htip).trans hball
    · exact radial_spur_exterior z x r α hx hr hα
  · intro y hy hout
    apply Set.subset_inter
    · exact ((convex_ball x ε).segment_subset htip (hy.trans_le (min_le_left _ _))).trans hball
    · rw [segment_symm]
      exact exterior_segment_of_dot z y (x+α • (x-z)) r hout
        (hσdot (hy.trans_le (min_le_right _ _))).le

end Zarankiewicz

end

end OAI
