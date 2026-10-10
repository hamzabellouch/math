import OAI.Combinatorics.ListHadwiger.Basic

namespace OAI

/-! Clique geometry of singleton and doubleton branches and finite clique-minor models. -/
namespace HadwigerMatching

variable {V : Type} {G : SimpleGraph V}

/-- A connected induced graph on precisely two vertices contains their edge. -/
theorem connected_card_two_isClique [DecidableEq V] (S : Finset V)
    (hS : S.card = 2) (hc : (G.induce (S : Set V)).Connected) :
    G.IsClique (S : Set V) := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
  have hedge : G.Adj a b := by
    let a' : ({a, b} : Finset V) := ⟨a, by simp⟩
    let b' : ({a, b} : Finset V) := ⟨b, by simp⟩
    have hne : a' ≠ b' := by
      intro h
      exact hab (congrArg Subtype.val h)
    obtain ⟨p⟩ := hc.preconnected a' b'
    have hadj := p.adj_snd (p.not_nil_of_ne hne)
    have hsnd : (p.snd : V) = a ∨ (p.snd : V) = b := by
      simpa using p.snd.property
    rcases hsnd with hsnd | hsnd
    · change G.Adj a (p.snd : V) at hadj
      rw [hsnd] at hadj
      exact (G.irrefl hadj).elim
    · simpa [a', hsnd] using hadj
  intro x hx y hy hxy
  have hx' : x = a ∨ x = b := by simpa using hx
  have hy' : y = a ∨ y = b := by simpa using hy
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
  · exact (hxy rfl).elim
  · exact hedge
  · exact hedge.symm
  · exact (hxy rfl).elim

/-- The vertices of singleton branches form a clique in `G`. -/
theorem singleton_vertices_isClique {ι : Type*} (B : ι → Set V)
    (htouch : ∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w) :
    G.IsClique {v | ∃ i, B i = {v}} := by
  rintro x ⟨i, hi⟩ y ⟨j, hj⟩ hxy
  have hij : i ≠ j := by
    intro h
    subst j
    have : x ∈ ({y} : Set V) := by rw [← hj, hi]; simp
    exact hxy (Set.mem_singleton_iff.mp this)
  obtain ⟨v, hv, w, hw, hvw⟩ := htouch i j hij
  have hvx : v = x := by simpa [hi] using hv
  have hwy : w = y := by simpa [hj] using hw
  simpa [hvx, hwy] using hvw

/-- On a finite vertex type, clique-minor branches can be represented by finite sets. -/
theorem finite_branch_model [Fintype V] {t : ℕ}
    (h : LinearListHadwiger.HasCliqueMinor G t) :
    ∃ B : Fin t → Finset V,
      (∀ i, (G.induce (B i : Set V)).Connected) ∧
      (∀ i, (B i).Nonempty) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (∀ i j, i ≠ j → ∃ v ∈ B i, ∃ w ∈ B j, G.Adj v w) := by
  classical
  obtain ⟨A, hconn, hdisj, htouch⟩ := h
  let B : Fin t → Finset V := fun i => (A i).toFinset
  have hcoe (i : Fin t) : (B i : Set V) = A i := by simp [B]
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hcoe]
    exact hconn i
  · intro i
    obtain ⟨v⟩ := (hconn i).nonempty
    exact ⟨v.val, Set.mem_toFinset.mpr v.property⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    exact Set.disjoint_left.mp (hdisj i j hij)
      (by simpa [B] using hvi) (by simpa [B] using hvj)
  · intro i j hij
    obtain ⟨v, hv, w, hw, hvw⟩ := htouch i j hij
    exact ⟨v, by simpa [B] using hv, w, by simpa [B] using hw, hvw⟩

end HadwigerMatching

end OAI
