import OAI.Combinatorics.Ramsey.CycleClique.Construction.WalkCycle
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.Nodup

namespace OAI

/-!
# Joining disjoint paths through a clique

The expansions of the chains of a path system are disjoint simple paths
with endpoints in the clique. Joining these paths, including any selected
singleton clique vertices, gives the exact cycle used in `path:interval`.
-/

namespace CycleClique.Construction
private theorem chain_of_pairwise {α : Type*} {R : α → α → Prop} {L : List α}
    (h : L.Pairwise R) : L.IsChain R := by
  induction h with
  | nil => exact .nil
  | @cons a l hrel _ ih =>
    exact ih.cons (fun b hb => hrel b (List.mem_of_mem_head? hb))

/-- Disjoint simple paths whose endpoints lie in a common clique can be
closed into a cycle through exactly all their vertices. -/
theorem hasCycle_of_disjoint_clique_paths {V : Type*} {G : SimpleGraph V}
    {Q : Set V} (hQ : G.IsClique Q) (L : List (List V))
    (hnonempty : ∀ l ∈ L, l ≠ [])
    (hpaths : ∀ l ∈ L, l.Nodup ∧ l.IsChain G.Adj)
    (hdisjoint : L.Pairwise List.Disjoint)
    (hendpoints : ∀ l ∈ L,
      (∀ v ∈ l.head?, v ∈ Q) ∧ (∀ v ∈ l.getLast?, v ∈ Q))
    (hlen : 3 ≤ L.flatten.length) : HasCycle G L.flatten.length := by
  have hflatne : L.flatten ≠ [] := by intro h; simp [h] at hlen
  have hLne : L ≠ [] := by intro h; simp [h] at hlen
  have hnodup : L.flatten.Nodup := List.nodup_flatten.mpr
    ⟨fun l hl => (hpaths l hl).1, hdisjoint⟩
  have hconnections : L.IsChain
      (fun l₁ l₂ => ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, G.Adj x y) := by
    apply chain_of_pairwise
    apply hdisjoint.imp_of_mem
    intro l₁ l₂ hl₁ hl₂ hd x hx y hy
    apply hQ ((hendpoints l₁ hl₁).2 x hx) ((hendpoints l₂ hl₂).1 y hy)
    intro heq
    subst y
    exact List.disjoint_left.mp hd (List.mem_of_mem_getLast? hx) (List.mem_of_mem_head? hy)
  have hchain : L.flatten.IsChain G.Adj :=
    (List.isChain_flatten (fun hempty => hnonempty [] hempty rfl)).mpr
      ⟨fun l hl => (hpaths l hl).2, hconnections⟩
  have hhead : L.flatten.head hflatne ∈ Q := by
    rw [List.head_flatten_eq_head_head hflatne (hnonempty _ (List.head_mem hLne))]
    apply (hendpoints _ (List.head_mem hLne)).1
    exact List.head?_eq_some_head (hnonempty _ (List.head_mem hLne))
  have hlast : L.flatten.getLast hflatne ∈ Q := by
    rw [List.getLast_flatten_eq_getLast_getLast hflatne
      (hnonempty _ (List.getLast_mem hLne))]
    apply (hendpoints _ (List.getLast_mem hLne)).2
    exact List.getLast?_eq_some_getLast (hnonempty _ (List.getLast_mem hLne))
  have hne : L.flatten.getLast hflatne ≠ L.flatten.head hflatne := by
    intro heq
    obtain ⟨v, hv⟩ := (hnodup.head_eq_getLast_iff hflatne).mp heq.symm
    simp [hv] at hlen
  let p := SimpleGraph.Walk.ofSupport L.flatten hflatne hchain
  have hp : p.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    simpa [p, SimpleGraph.Walk.support_ofSupport] using hnodup
  have hplength : p.length = L.flatten.length - 1 :=
    SimpleGraph.Walk.length_ofSupport hflatne hchain
  have hc := hasCycle_of_path_close hp (by omega) (hQ hlast hhead hne)
  have heq : p.length + 1 = L.flatten.length := by omega
  simpa [heq] using hc

end CycleClique.Construction

end OAI
