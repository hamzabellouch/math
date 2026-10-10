import OAI.Combinatorics.ListHadwiger.PairedSources

namespace OAI

namespace LinearListHadwiger.Assembly
open SimpleGraph
variable {V I O : Type} (G : SimpleGraph V)

lemma connected_glue (C : Set V) (B : O → Set V)
    (hC : (G.induce C).Connected)
    (hB : ∀ o, (G.induce (B o)).Connected)
    (hE : ∀ o, ∃ x ∈ B o, ∃ y ∈ C, G.Adj x y) :
    (G.induce (C ∪ {v | ∃ o, v ∈ B o})).Connected := by
  let S := C ∪ {v | ∃ o, v ∈ B o}
  have hCS : C ⊆ S := Set.subset_union_left
  obtain ⟨root⟩ := hC.nonempty
  have hreach : ∀ v : S, (G.induce S).Reachable v ⟨root.val,hCS root.property⟩ := by
    rintro ⟨v,hv⟩
    rcases hv with hv | ⟨o,hv⟩
    · exact (hC.preconnected ⟨v,hv⟩ root).map (G.induceHomOfLE hCS).toHom
    · obtain ⟨x,hx,y,hy,hxy⟩ := hE o
      have hBS : B o ⊆ S := fun _ hw => Or.inr ⟨o,hw⟩
      have h₁ := ((hB o).preconnected ⟨v,hv⟩ ⟨x,hx⟩).map
        (G.induceHomOfLE hBS).toHom
      have h₂ : (G.induce S).Adj ⟨x,hBS hx⟩ ⟨y,hCS hy⟩ := hxy
      have h₃ := (hC.preconnected ⟨y,hy⟩ root).map (G.induceHomOfLE hCS).toHom
      exact h₁.trans (h₂.reachable.trans h₃)
  refine { preconnected := ?_, nonempty := ⟨⟨root.val,hCS root.property⟩⟩ }
  intro v w
  exact (hreach v).trans (hreach w).symm

theorem clique_of_occurrences {t : ℕ} (label : O → Fin t)
    (B : O → Set V) (C : Fin t → Set V)
    (hB : ∀ o, (G.induce (B o)).Connected)
    (hC : ∀ i, (G.induce (C i)).Connected)
    (hBB : ∀ o p, label o ≠ label p → Disjoint (B o) (B p))
    (hCC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hBC : ∀ o i, Disjoint (B o) (C i))
    (hattach : ∀ o, ∃ x ∈ B o, ∃ y ∈ C (label o), G.Adj x y)
    (hpairs : ∀ i j, i ≠ j → ∃ o p, label o = i ∧ label p = j ∧
      ∃ x ∈ B o, ∃ y ∈ B p, G.Adj x y) :
    HasCliqueMinor G t := by
  let S (i : Fin t) := C i ∪ {v | ∃ o, label o = i ∧ v ∈ B o}
  refine ⟨S,?_,?_,?_⟩
  · intro i
    have hh := connected_glue G (C i) (fun o : {o // label o = i} => B o.val)
      (hC i) (fun o => hB o.val) (fun o => by simpa [o.property] using hattach o.val)
    have he : S i = C i ∪ {v | ∃ o : {o // label o = i}, v ∈ B o.val} := by
      ext v
      simp only [S,Set.mem_union,Set.mem_ofPred_eq,Subtype.exists]
      aesop
    change (G.induce (S i)).Connected
    rw [he]
    exact hh
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    rcases hvi with hi | ⟨o,ho,hi⟩ <;> rcases hvj with hj | ⟨p,hp,hj⟩
    · exact Set.disjoint_left.mp (hCC i j hij) hi hj
    · exact Set.disjoint_left.mp (hBC p i) hj hi
    · exact Set.disjoint_left.mp (hBC o j) hi hj
    · exact Set.disjoint_left.mp (hBB o p (by simpa [ho,hp] using hij)) hi hj
  · intro i j hij
    obtain ⟨o,p,ho,hp,x,hx,y,hy,hxy⟩ := hpairs i j hij
    exact ⟨x,Or.inr ⟨o,ho,hx⟩,y,Or.inr ⟨p,hp,hy⟩,hxy⟩

lemma attach_ports [Fintype V] [Fintype O] [DecidableEq V] [DecidableRel G.Adj]
    (port : O → V) (U : Finset V)
    (hN : ∀ o, Fintype.card O ≤ (U.filter (fun v => G.Adj (port o) v)).card) :
    ∃ nbr : O → V, Function.Injective nbr ∧ ∀ o, nbr o ∈ U ∧ G.Adj (port o) (nbr o) := by
  classical
  let N (o : O) := U.filter (fun v => G.Adj (port o) v)
  have hall : ∀ S : Finset O, S.card ≤ (S.biUnion N).card := by
    intro S
    obtain rfl | hS := S.eq_empty_or_nonempty
    · simp
    obtain ⟨o,ho⟩ := hS
    exact (Finset.card_le_univ S).trans ((hN o).trans
      (Finset.card_le_card (Finset.subset_biUnion_of_mem N ho)))
  obtain ⟨nbr,hi,hn⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective N).mp hall
  exact ⟨nbr,hi,fun o => Finset.mem_filter.mp (hn o)⟩

end LinearListHadwiger.Assembly

end OAI
