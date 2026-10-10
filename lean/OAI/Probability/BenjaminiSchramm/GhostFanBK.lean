import OAI.Probability.BenjaminiSchramm.GhostFan
import OAI.Probability.BenjaminiSchramm.GhostBondBK

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical

namespace Percolation.BenjaminiSchramm

variable {V E T : Type*} (G : BondGraph V E) (x : V) (vertex : T → V)

lemma ghostFan_mem_disjointOccurrence {ω : Set E} {m n : Set T}
    (h : GhostFan (openSimpleGraph G ω) (vertex '' m) (vertex '' n) x) :
    ω ∈ DisjointOccurrence (finiteGhostConnection G x vertex m)
      (finiteGhostConnection G x vertex n) := by
  obtain ⟨a,⟨i,hi,rfl⟩,b,⟨j,hj,rfl⟩,p,q,hpq⟩ := h
  obtain ⟨s,hs,hse,hso⟩ := walk_lift_bonds G ω p
  obtain ⟨t,ht,hte,hto⟩ := walk_lift_bonds G ω q
  refine ⟨s.toFinset,t.toFinset,?_,?_,?_,?_,?_⟩
  · intro e he
    exact hso e (List.mem_toFinset.mp he)
  · intro e he
    exact hto e (List.mem_toFinset.mp he)
  · apply Finset.disjoint_left.mpr
    intro e hes het
    exact List.disjoint_left.mp hpq
      (hse ▸ List.mem_map_of_mem (List.mem_toFinset.mp hes))
      (hte ▸ List.mem_map_of_mem (List.mem_toFinset.mp het))
  · exact ⟨i,hi,hs.conn (fun e he => List.mem_toFinset.mpr he)⟩
  · exact ⟨j,hj,ht.conn (fun e he => List.mem_toFinset.mpr he)⟩

lemma ghostFan_measure_le [Countable E] (p : unitInterval) (m n : Set T) :
    (law p) {ω | GhostFan (openSimpleGraph G ω) (vertex '' m) (vertex '' n) x} ≤
      (law p) (finiteGhostConnection G x vertex m) *
        (law p) (finiteGhostConnection G x vertex n) := by
  calc
    _ ≤ (law p) (DisjointOccurrence (finiteGhostConnection G x vertex m)
        (finiteGhostConnection G x vertex n)) :=
      measure_mono (fun _ h => ghostFan_mem_disjointOccurrence G x vertex h)
    _ ≤ _ := bk_ennreal p _ _
      (finiteGhostConnection_upper G x vertex m) (finiteGhostConnection_upper G x vertex n)
      (finiteGhostConnection_finiteWitness G x vertex m)
      (finiteGhostConnection_finiteWitness G x vertex n)

end Percolation.BenjaminiSchramm

end

end OAI
