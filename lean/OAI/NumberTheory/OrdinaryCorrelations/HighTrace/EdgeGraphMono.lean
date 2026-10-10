import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EdgeGraph

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace Finset Classical SimpleGraph
noncomputable section
variable {h ℓ : ℕ}

lemma edgeGraph_mono (w : ClosedLine h ℓ) (hh : 0<h) {E F : Finset (Fin ℓ)} (hEF : E⊆F) :
    edgeGraph w hh E ≤ edgeGraph w hh F := by
  rintro x y ⟨e,he,hor⟩
  exact ⟨e,hEF he,hor⟩

lemma edgeGraph_insert (w : ClosedLine h ℓ) (hh : 0<h) (E : Finset (Fin ℓ)) (e : Fin ℓ) :
    edgeGraph w hh (insert e E)=edgeGraph w hh E ⊔ SimpleGraph.edge (w.offset e.castSucc) (w.offset e.succ) := by
  ext u v
  simp only [edgeGraph,sup_adj,SimpleGraph.edge_adj,mem_insert]
  constructor
  · rintro ⟨j,hj,hor⟩
    rcases hj with he|hj
    · subst j
      right
      rcases hor with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨Or.inl ⟨rfl,rfl⟩,w.endpoints_ne hh e⟩
      · exact ⟨Or.inr ⟨rfl,rfl⟩,(w.endpoints_ne hh e).symm⟩
    · exact Or.inl ⟨j,hj,hor⟩
  · rintro (⟨j,hj,hor⟩|⟨hor,hne⟩)
    · exact ⟨j,Or.inr hj,hor⟩
    · refine ⟨e,Or.inl rfl,?_⟩
      rcases hor with h|h
      · exact Or.inl h
      · exact Or.inr ⟨h.2,h.1⟩

theorem edgeGraph_acyclic (w : ClosedLine h ℓ) (hh : 0<h) (E : Finset (Fin ℓ))
    (hE : E⊆w.treeSteps) : (edgeGraph w hh E).IsAcyclic := by
  induction E using Finset.strongInductionOn
  rename_i E ih
  by_cases hne : E.Nonempty
  · let e := E.max' hne
    have he : e∈E := max'_mem _ _
    have hnew := (mem_filter.mp (hE he)).2
    have hsub : E.erase e ⊂ E := erase_ssubset he
    have hac := ih (E.erase e) hsub (fun j hj => hE (mem_of_mem_erase hj))
    have hiso : (edgeGraph w hh (E.erase e)).neighborSet (w.offset e.succ)=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨j,hj,hor|hor⟩
      · have hje : j.val<e.val := by
          have hm := le_max' E j (mem_of_mem_erase hj)
          have hn := (mem_erase.mp hj).1
          exact lt_of_le_of_ne hm (fun he => hn (Fin.ext he))
        exact hnew j.castSucc (by simpa using hje.le) hor.1.symm
      · have hje : j.val<e.val := by
          have hm := le_max' E j (mem_of_mem_erase hj)
          have hn := (mem_erase.mp hj).1
          exact lt_of_le_of_ne hm (fun he => hn (Fin.ext he))
        exact hnew j.succ (by simpa using hje) hor.2.symm
    have hnr := not_reachable_of_neighborSet_right_eq_empty (w.endpoints_ne hh e) hiso
    have hins : insert e (E.erase e)=E := insert_erase he
    rw [←hins,edgeGraph_insert]
    exact hac.sup_edge_of_not_reachable hnr
  · have hz : E=∅ := not_nonempty_iff_eq_empty.mp hne
    subst E
    have hg : edgeGraph w hh ∅=⊥ := by ext x y; simp [edgeGraph]
    rw [hg]
    exact isAcyclic_bot

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
