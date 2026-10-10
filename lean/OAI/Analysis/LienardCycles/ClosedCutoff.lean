import OAI.Analysis.LienardCycles.PhysicalFlow

namespace OAI

universe uE

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff NNReal

open Set Filter
open scoped Topology NNReal
namespace QuinticLienard
open GlobalODE
lemma flow_periodic_of_hit {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (W : E → E) {K L : ℝ≥0} (hK : LipschitzWith K W) (hL : ∀ x,‖W x‖≤L)
    {x : E} {T : ℝ} (he : flow W hK hL x T=x) : Function.Periodic (flow W hK hL x) T := by
  intro t
  rw [add_comm,flow_add,he]
lemma flow_true_of_closed {F : Polynomial ℝ} (W : Plane → Plane) {K L : ℝ≥0}
    (hK : LipschitzWith K W) (hL : ∀ x,‖W x‖≤L) {x : Plane} {T : ℝ}
    (hT : 0<T) (he : flow W hK hL x T=x)
    (hW : ∀ t ∈ Icc 0 T,W (flow W hK hL x t)=vectorField F (flow W hK hL x t)) :
    IsSolution F (flow W hK hL x) := by
  have hp := flow_periodic_of_hit W hK hL he
  intro t
  have ht : flow W hK hL x t ∈ flow W hK hL x '' Icc 0 T := by
    rw [show Icc 0 T=Icc 0 (0+T) by simp,hp.image_Icc hT 0]
    exact mem_range_self t
  obtain ⟨s,hs,heq⟩ := ht
  have hd := flow_deriv W hK hL x t
  rwa [←heq,hW s hs,heq] at hd
lemma periodic_range_subset {z : ℝ → Plane} {T : ℝ} (hp : Function.Periodic z T) (hT : 0<T)
    {U : Set Plane} (hU : ∀ t ∈ Icc 0 T,z t ∈ U) : range z ⊆ U := by
  rw [←hp.image_Icc hT 0]
  rintro p ⟨t,ht,rfl⟩
  exact hU t (by simpa using ht)
end QuinticLienard

end OAI
