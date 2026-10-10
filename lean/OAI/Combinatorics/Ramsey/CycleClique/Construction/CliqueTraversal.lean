import OAI.Combinatorics.Ramsey.CycleClique.Construction.LongestPaths
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange

namespace OAI

/-! Simple paths through all clique vertices with prescribed distinct ends. -/

namespace CycleClique.Construction
theorem indexedPath_ofFn_chain {V : Type*} {G : SimpleGraph V} {r : ℕ}
    {f : Fin (r + 1) → V} (hf : IsIndexedPath G f) :
    (List.ofFn f).Nodup ∧ (List.ofFn f).IsChain G.Adj := by
  refine ⟨List.nodup_ofFn.mpr hf.1, List.isChain_ofFn.mpr ?_⟩
  intro i hi
  exact hf.2 ⟨i, by omega⟩

theorem indexedPath_of_list {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (L : List V) (hL : L.Nodup) (hchain : L.IsChain G.Adj) (hlen : L.length = r + 1) :
    IsIndexedPath G (fun i : Fin (r + 1) => L.get (Fin.cast hlen.symm i)) := by
  refine ⟨hL.injective_get.comp (Fin.cast_injective _), ?_⟩
  intro i
  exact (List.isChain_iff_getElem.mp hchain) i.val (by have := i.isLt; omega)

private theorem chain_of_pairwise {V : Type*} {R : V → V → Prop} {L : List V}
    (h : L.Pairwise R) : L.IsChain R := by
  induction h with
  | nil => exact .nil
  | @cons a l hrel _ ih =>
    exact ih.cons (fun b hb => hrel b (List.mem_of_mem_head? hb))

theorem chain_of_clique_nodup {V : Type*} {G : SimpleGraph V} {E : Finset V}
    (hclique : G.IsClique (E : Set V)) {L : List V} (hL : L.Nodup)
    (hmem : ∀ v ∈ L, v ∈ E) : L.IsChain G.Adj := by
  apply chain_of_pairwise
  exact hL.pairwise_of_forall_ne
    (fun a ha b hb hab => hclique (hmem a ha) (hmem b hb) hab)

theorem exists_clique_traversal {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {E : Finset V} (hclique : G.IsClique (E : Set V))
    {a b : V} (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b) :
    ∃ L : List V, L.Nodup ∧ L.IsChain G.Adj ∧ L.length = E.card ∧
      L.head? = some a ∧ L.getLast? = some b ∧ ∀ v ∈ L, v ∈ E := by
  classical
  let M := ((E.erase a).erase b).toList
  let L := a :: (M ++ [b])
  have hM : ∀ v ∈ M, v ∈ E ∧ v ≠ a ∧ v ≠ b := by
    intro v hv
    have hm : v ∈ (E.erase a).erase b := by simpa [M] using hv
    exact ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm),
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase hm)).1,
      (Finset.mem_erase.mp hm).1⟩
  have hL : L.Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · intro h
      rcases List.mem_append.mp h with h | h
      · exact (hM a h).2.1 rfl
      · have heq : a = b := by simpa using h
        exact hab heq
    · apply List.nodup_append.mpr
      refine ⟨Finset.nodup_toList _, by simp, ?_⟩
      intro v hv b' hb' heq
      have hb'eq : b' = b := by simpa using hb'
      exact (hM v hv).2.2 (heq.trans hb'eq)
  have hmem : ∀ v ∈ L, v ∈ E := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ha
    · rcases List.mem_append.mp hv with hv | hv
      · exact (hM v hv).1
      · have heq : v = b := by simpa using hv
        exact heq ▸ hb
  have hlen : L.length = E.card := by
    have hea := Finset.card_erase_add_one ha
    have hba : b ∈ E.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
    have heb := Finset.card_erase_add_one hba
    dsimp [L, M]
    simp only [List.length_cons, List.length_append, Finset.length_toList, List.length_nil]
    omega
  exact ⟨L, hL, chain_of_clique_nodup hclique hL hmem, hlen, rfl,
    by
      change ((a :: M) ++ [b]).getLast? = some b
      exact List.getLast?_append_cons (a :: M) b [], hmem⟩

end CycleClique.Construction

end OAI
