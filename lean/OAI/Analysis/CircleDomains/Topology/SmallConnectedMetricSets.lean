import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith

namespace OAI

/-! The small connected sets and finite chains used to construct arcs in a
compact locally connected metric space. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_uniform_small_connected_sets
    (X : Type*) [MetricSpace X] [CompactSpace X] [LocallyConnectedSpace X]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : X, dist x y < δ →
      ∃ V : Set X, IsConnected V ∧ x ∈ V ∧ y ∈ V ∧
        ∀ a ∈ V, ∀ b ∈ V, dist a b < ε := by
  choose U hUsub hUopen hxU hUconn using fun x : X =>
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp
      (inferInstance : LocallyConnectedSpace X) x (ball x (ε / 2))
      (ball_mem_nhds x (by linarith))
  have hcover : (univ : Set X) ⊆ ⋃ x, U x := fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨δ, hδ, hcoverδ⟩ := lebesgue_number_lemma_of_metric isCompact_univ hUopen hcover
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  obtain ⟨c, hc⟩ := hcoverδ x (mem_univ x)
  refine ⟨U c, hUconn c, hc (mem_ball_self hδ), hc ?_, ?_⟩
  · exact mem_ball.mpr (by simpa only [dist_comm] using hxy)
  · intro a ha b hb
    have ha' := mem_ball.mp (hUsub c ha)
    have hb' := mem_ball.mp (hUsub c hb)
    have ht := dist_triangle a c b
    rw [dist_comm c b] at ht
    linarith

lemma metric_connected_reflTransGen
    {X : Type*} [MetricSpace X] [PreconnectedSpace X] {ε : ℝ} (hε : 0 < ε) (x y : X) :
    Relation.ReflTransGen (fun a b : X => dist a b < ε) x y := by
  let S := {z : X | Relation.ReflTransGen (fun a b : X => dist a b < ε) x z}
  have hS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    apply Filter.mem_of_superset (ball_mem_nhds z hε)
    intro w hw
    exact hz.tail (by simpa only [mem_ball, dist_comm] using hw)
  have hSc : IsOpen Sᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    apply Filter.mem_of_superset (ball_mem_nhds z hε)
    intro w hw hwS
    exact hz (hwS.tail (mem_ball.mp hw))
  have hclosed : IsClosed S := by simpa only [compl_compl] using hSc.isClosed_compl
  have hEq : S = univ := (show IsClopen S from ⟨hclosed, hS⟩).eq_univ
    ⟨x, Relation.ReflTransGen.refl⟩
  exact (Set.eq_univ_iff_forall.mp hEq) y

lemma connected_set_metric_chain
    {X : Type*} [MetricSpace X] {S : Set X} (hS : IsConnected S)
    {ε : ℝ} (hε : 0 < ε) (x y : S) :
    Relation.ReflTransGen (fun a b : S => dist (a : X) (b : X) < ε) x y := by
  let : ConnectedSpace S := isConnected_iff_connectedSpace.mp hS
  exact metric_connected_reflTransGen hε x y

end CircleDomainRigidity

end

end OAI
