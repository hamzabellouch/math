import OAI.Combinatorics.Ramsey.CycleClique.Construction.PathSystem

namespace OAI

/-! Remove isolated clique vertices from a list of expanded chains. This
permits path surgery to retain singleton pieces until its final step. -/

namespace CycleClique.Construction
variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

theorem short_chain_in_clique {l : List V}
    (hends : (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q)))
    (hlen : l.length < 3) : ∀ v ∈ l, v ∈ Q := by
  cases l with
  | nil => simp
  | cons x l =>
    cases l with
    | nil => simpa using hends.1
    | cons y l =>
      cases l with
      | nil =>
        have hx : x ∈ Q := hends.1 x (by simp)
        have hy : y ∈ Q := hends.2 y (by simp)
        have hxy : ¬ (x ∈ Q ∧ y ∈ Q) := by simpa using hsteps
        exact False.elim (hxy ⟨hx, hy⟩)
      | cons z l => simp only [List.length_cons] at hlen; omega

noncomputable def normalizeChains (C : List (List V))
    (hpaths : ∀ l ∈ C, l.Nodup ∧ l.IsChain G.Adj)
    (hdis : C.Pairwise List.Disjoint)
    (hends : ∀ l ∈ C, (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : ∀ l ∈ C, l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    ExpandedPathSystem G Q where
  chains := C.filter (fun l => decide (3 ≤ l.length))
  nontrivial := by
    intro l hl
    exact of_decide_eq_true (List.mem_filter.mp hl).2
  paths := fun l hl => hpaths l (List.mem_filter.mp hl).1
  disjoint := hdis.filter _
  endpoints := fun l hl => hends l (List.mem_filter.mp hl).1
  no_clique_steps := fun l hl => hsteps l (List.mem_filter.mp hl).1

theorem normalizeChains_outside_vertices [DecidableEq V] (C : List (List V))
    (hpaths : ∀ l ∈ C, l.Nodup ∧ l.IsChain G.Adj)
    (hdis : C.Pairwise List.Disjoint)
    (hends : ∀ l ∈ C, (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : ∀ l ∈ C, l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    (normalizeChains C hpaths hdis hends hsteps).vertices \ Q = C.flatten.toFinset \ Q := by
  ext v
  simp only [Finset.mem_sdiff, ExpandedPathSystem.vertices, normalizeChains,
    List.mem_toFinset, List.mem_flatten, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨l, ⟨hl, _⟩, hv⟩, hvQ⟩
    exact ⟨⟨l, hl, hv⟩, hvQ⟩
  · rintro ⟨⟨l, hl, hv⟩, hvQ⟩
    have hlen : 3 ≤ l.length := by
      by_contra hn
      exact hvQ (short_chain_in_clique (hends l hl) (hsteps l hl) (by omega) v hv)
    exact ⟨⟨l, ⟨hl, hlen⟩, hv⟩, hvQ⟩

theorem normalizeChains_amount [DecidableEq V] (C : List (List V))
    (hpaths : ∀ l ∈ C, l.Nodup ∧ l.IsChain G.Adj)
    (hdis : C.Pairwise List.Disjoint)
    (hends : ∀ l ∈ C, (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hsteps : ∀ l ∈ C, l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    (normalizeChains C hpaths hdis hends hsteps).amount = (C.flatten.toFinset \ Q).card := by
  classical
  unfold ExpandedPathSystem.amount
  convert congrArg Finset.card
    (@normalizeChains_outside_vertices V G Q (Classical.decEq V) C
      hpaths hdis hends hsteps) using 1
  congr 1
  ext v
  simp

end CycleClique.Construction

end OAI
