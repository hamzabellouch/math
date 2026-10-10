import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.ForestTraversal
open Classical SimpleGraph
noncomputable section
variable {V : Type*} {G H : SimpleGraph V}

lemma avoid_edge_suffix {a b s t : V}
    (hremove : ∀ {u v},G.Adj u v → ¬H.Adj u v →
      (u=a ∧ v=b) ∨ (u=b ∧ v=a)) (p : G.Walk s t) :
    ∃ u,(u=s ∨ u=a ∨ u=b) ∧ ∃ q : H.Walk u t,q.length ≤ p.length := by
  induction p with
  | @nil s => exact ⟨s,Or.inl rfl,.nil,le_rfl⟩
  | @cons s v t ha p ih =>
    obtain ⟨u,hu,q,hq⟩ := ih
    rcases hu with huv | hu
    · subst u
      by_cases hh : H.Adj s v
      · exact ⟨s,Or.inl rfl,.cons hh q,Nat.succ_le_succ hq⟩
      · have hv : v=a ∨ v=b := by
          rcases hremove ha hh with hab | hba
          · exact Or.inr hab.2
          · exact Or.inl hba.2
        exact ⟨v,Or.inr hv,q,hq.trans (Nat.le_succ _)⟩
    · exact ⟨u,Or.inr hu,q,hq.trans (Nat.le_succ _)⟩

end
end OrdinaryCorrelations.ForestTraversal

end

end OAI
