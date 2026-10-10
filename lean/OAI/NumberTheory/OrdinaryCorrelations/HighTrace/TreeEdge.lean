import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Directed

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical SimpleGraph
noncomputable section
variable {h ℓ : ℕ}

def treeEdge (w : ClosedLine h ℓ) (e : Fin ℓ) : Sym2 ℤ :=
  s(w.offset e.castSucc,w.offset e.succ)

lemma grows_full_tree (w : ClosedLine h ℓ) : Grows w 0 w.treeSteps := by
  refine ⟨Subset.rfl,?_⟩
  intro e he
  by_cases hz : w.offset e.castSucc=0
  · exact Or.inl hz
  · obtain ⟨j,hj,hjv⟩ := has_incoming_edge w (w.offset e.castSucc) (departure_mem_vertices w e) hz
    exact Or.inr ⟨j,hj,incoming_earlier w hj hjv,hjv⟩

lemma reached_full_tree (w : ClosedLine h ℓ) : reached w 0 w.treeSteps=treeVertices w := by
  apply Finset.ext
  intro v
  constructor
  · intro hv
    rcases mem_insert.mp hv with rfl | hv
    · exact mem_image.mpr ⟨0,mem_univ _,w.start_zero⟩
    · obtain ⟨e,he,rfl⟩ := mem_image.mp hv
      exact endpoint_mem_vertices w e
  · intro hv
    by_cases hz : v=0
    · rw [hz]; exact mem_insert_self _ _
    · obtain ⟨e,he,hev⟩ := has_incoming_edge w v hv hz
      exact mem_insert_of_mem (mem_image.mpr ⟨e,he,hev⟩)

theorem grown_tour (w : ClosedLine h ℓ) (hh : 0<h) (v : ℤ) (E : Finset (Fin ℓ))
    (hg : Grows w v E) :
    ∃ p : (edgeGraph w hh w.treeSteps).Walk v v,
      p.length=2*E.card ∧ (∀ z ∈ reached w v E,z ∈ p.support) ∧
      ∀ q : Sym2 ℤ,p.edges.count q=2*(E.filter (fun e => treeEdge w e=q)).card := by
  suffices aux : ∀ n,∀ E : Finset (Fin ℓ),E.card=n → Grows w v E →
      ∃ p : (edgeGraph w hh w.treeSteps).Walk v v,
        p.length=2*E.card ∧ (∀ z ∈ reached w v E,z ∈ p.support) ∧
        ∀ q : Sym2 ℤ,p.edges.count q=2*(E.filter (fun e => treeEdge w e=q)).card by
    exact aux _ E rfl hg
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E hcard hg
    by_cases hne : E.Nonempty
    · let e := E.max' hne
      have he : e ∈ E := max'_mem E hne
      let F := E.erase e
      have hF : F ⊆ E := erase_subset _ _
      have heF : e ∉ F := notMem_erase _ _
      have hinsert : insert e F=E := insert_erase he
      have hFgrow : Grows w v F := by
        refine ⟨hF.trans hg.1,?_⟩
        intro f hf
        rcases hg.2 f (hF hf) with hr | ⟨j,hj,hjf,hjv⟩
        · exact Or.inl hr
        · refine Or.inr ⟨j,mem_erase.mpr ⟨?_,hj⟩,hjf,hjv⟩
          intro hje
          subst j
          exact (not_lt_of_ge (le_max' E f (hF hf))) hjf
      have hlt : F.card<n := by rw [←hcard]; exact card_erase_lt_of_mem he
      obtain ⟨p,hplen,hcover,hcount⟩ := ih F.card hlt F rfl hFgrow
      have hsource : w.offset e.castSucc ∈ reached w v F := by
        rcases hg.2 e he with hr | ⟨j,hj,hje,hjv⟩
        · rw [hr]; exact mem_insert_self _ _
        · exact mem_insert_of_mem (mem_image.mpr ⟨j,mem_erase.mpr ⟨ne_of_lt hje,hj⟩,hjv⟩)
      obtain ⟨p₁,p₂,hp⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp
        (hcover _ hsource)
      let ha := edgeGraph_adj w hh w.treeSteps e (hg.1 he)
      let loop : (edgeGraph w hh w.treeSteps).Walk (w.offset e.castSucc) (w.offset e.castSucc) :=
        .cons ha (.cons ha.symm .nil)
      let q := p₁.append (loop.append p₂)
      refine ⟨q,?_,?_,?_⟩
      · have hcard' : E.card=F.card+1 := by rw [←hinsert,card_insert_of_notMem heF]
        rw [hp,SimpleGraph.Walk.length_append] at hplen
        simp only [q,loop,SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons,
          SimpleGraph.Walk.length_nil]
        omega
      · intro z hz
        rcases mem_insert.mp hz with hroot | hz
        · subst z; exact q.start_mem_support
        · obtain ⟨f,hf,rfl⟩ := mem_image.mp hz
          by_cases hfe : f=e
          · subst f
            exact (SimpleGraph.Walk.mem_support_append_iff p₁ (loop.append p₂)).mpr
              (Or.inr ((SimpleGraph.Walk.mem_support_append_iff loop p₂).mpr
                (Or.inl (by simp [loop]))))
          · have hmem := hcover (w.offset f.succ) (mem_insert_of_mem (mem_image.mpr ⟨f,mem_erase.mpr ⟨hfe,hf⟩,rfl⟩))
            rw [hp,SimpleGraph.Walk.mem_support_append_iff] at hmem
            exact (SimpleGraph.Walk.mem_support_append_iff p₁ (loop.append p₂)).mpr
              (hmem.imp_right (fun hh => (SimpleGraph.Walk.mem_support_append_iff loop p₂).mpr (Or.inr hh)))
      · intro s
        have hc := hcount s
        rw [hp,SimpleGraph.Walk.edges_append,List.count_append] at hc
        have hsame : s(w.offset e.castSucc,w.offset e.succ)=treeEdge w e := rfl
        have hsym : s(w.offset e.succ,w.offset e.castSucc)=treeEdge w e := Sym2.eq_swap
        have hef : e ∉ F.filter (fun e => treeEdge w e=s) := fun he => heF (mem_filter.mp he).1
        have heqcard : (E.filter (fun e => treeEdge w e=s)).card =
            (F.filter (fun e => treeEdge w e=s)).card + if treeEdge w e=s then 1 else 0 := by
          rw [←hinsert,filter_insert]
          split_ifs <;> simp [hef]
        rw [heqcard]
        simp only [q,loop,SimpleGraph.Walk.edges_append,SimpleGraph.Walk.edges_cons,
          SimpleGraph.Walk.edges_nil,List.count_append,hsame,hsym]
        by_cases hes : treeEdge w e=s
        · subst s
          simp only [List.count_cons_self,List.count_nil,ite_true]
          omega
        · have hse : s≠treeEdge w e := Ne.symm hes
          simp only [List.count_cons_of_ne hes,List.count_nil,hes,ite_false]
          omega
    · have hE : E=∅ := not_nonempty_iff_eq_empty.mp hne
      subst E
      refine ⟨.nil,by simp,?_,by simp⟩
      intro z hz
      simpa [reached] using hz

end
end OrdinaryCorrelations.NumericalSubtrees

end

end OAI
