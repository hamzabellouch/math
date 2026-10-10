import OAI.Probability.FreeIsing.Trees.ConnectedHull
import OAI.Probability.FreeIsing.Trees.Parents
import OAI.Probability.FreeIsing.Trees.Transitivity

namespace OAI

namespace Problem367

namespace TreeAut

private theorem length_le_of_root_eq {d : ℕ} (g : TreeAut d)
    (hg : g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d)
    (v : TreeVertex d) : (g.toEquiv v).1.length ≤ v.1.length := by
  suffices h : ∀ n (v : TreeVertex d), v.1.length = n →
      (g.toEquiv v).1.length ≤ n from h _ v rfl
  intro n
  induction n with
  | zero =>
      intro v hv
      have heq : v = ConnectedHull.root d :=
        Subtype.ext (List.length_eq_zero_iff.mp hv)
      rw [heq, hg]
      exact Nat.zero_le _
  | succ n ih =>
      intro v hv
      have hne : v.1 ≠ [] := by
        intro heq
        simp [heq] at hv
      have hp : (parentVertex v).1.length = n := by
        rw [parentVertex_length, hv]
        omega
      have hbound := ih (parentVertex v) hp
      have hadj := treeAdj_length
        ((g.map_adj _ _).mpr (treeAdj_parentVertex hne))
      omega

theorem length_eq_of_root_eq {d : ℕ} (g : TreeAut d)
    (hg : g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d)
    (v : TreeVertex d) : (g.toEquiv v).1.length = v.1.length := by
  have hsymm : g.symm.toEquiv (ConnectedHull.root d) = ConnectedHull.root d := by
    change g.toEquiv.symm (ConnectedHull.root d) = ConnectedHull.root d
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact hg.symm
  apply Nat.le_antisymm (length_le_of_root_eq g hg v)
  simpa only [TreeAut.symm, Equiv.symm_apply_apply] using
    length_le_of_root_eq g.symm hsymm (g.toEquiv v)

theorem root_eq_of_length_preserving {d : ℕ} (g : TreeAut d)
    (hg : ∀ v, (g.toEquiv v).1.length = v.1.length) :
    g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d := by
  apply Subtype.ext
  apply List.length_eq_zero_iff.mp
  exact hg (ConnectedHull.root d)

theorem symm_length_eq {d : ℕ} (g : TreeAut d)
    (hg : ∀ v, (g.toEquiv v).1.length = v.1.length) (v : TreeVertex d) :
    (g.toEquiv.symm v).1.length = v.1.length := by
  simpa only [Equiv.apply_symm_apply] using (hg (g.toEquiv.symm v)).symm

theorem map_takeVertex_of_length_preserving {d : ℕ} (g : TreeAut d)
    (hg : ∀ v, (g.toEquiv v).1.length = v.1.length)
    (v : TreeVertex d) (n : ℕ) :
    g.toEquiv (ConnectedHull.takeVertex v n) =
      ConnectedHull.takeVertex (g.toEquiv v) n := by
  by_cases hn : n ≤ v.1.length
  · induction hn using Nat.decreasingInduction with
    | self =>
        rw [ConnectedHull.prefix_length, ← hg v, ConnectedHull.prefix_length]
    | of_succ k hk ih =>
        apply treeAdj_lower_unique
          ((g.map_adj _ _).mpr (ConnectedHull.prefix_adj v hk))
        · rw [ih]
          apply ConnectedHull.prefix_adj
          rw [hg]
          exact hk
        · rw [hg, hg]
          simp only [ConnectedHull.takeVertex, List.length_take]
          omega
        · rw [hg]
          simp only [ConnectedHull.takeVertex, List.length_take, hg]
          omega
  · have hv : ConnectedHull.takeVertex v n = v := by
      apply Subtype.ext
      exact (List.take_eq_self_iff v.1).mpr (by omega)
    have hgv : ConnectedHull.takeVertex (g.toEquiv v) n = g.toEquiv v := by
      apply Subtype.ext
      apply (List.take_eq_self_iff (g.toEquiv v).1).mpr
      rw [hg]
      omega
    rw [hv, hgv]

theorem map_prefixes_of_map_endpoint {d : ℕ} (g : TreeAut d)
    (hg : ∀ v, (g.toEquiv v).1.length = v.1.length)
    {u v : TreeVertex d} (huv : g.toEquiv u = v) (n : ℕ) :
    g.toEquiv (ConnectedHull.takeVertex u n) = ConnectedHull.takeVertex v n := by
  rw [map_takeVertex_of_length_preserving g hg, huv]

theorem map_takeVertex_of_root_eq {d : ℕ} (g : TreeAut d)
    (hg : g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d)
    (v : TreeVertex d) (n : ℕ) :
    g.toEquiv (ConnectedHull.takeVertex v n) =
      ConnectedHull.takeVertex (g.toEquiv v) n :=
  map_takeVertex_of_length_preserving g (length_eq_of_root_eq g hg) v n

theorem map_prefix_iff_of_length_preserving {d : ℕ} (g : TreeAut d)
    (hg : ∀ v, (g.toEquiv v).1.length = v.1.length)
    (u v : TreeVertex d) :
    (g.toEquiv u).1 <+: (g.toEquiv v).1 ↔ u.1 <+: v.1 := by
  have forward : ∀ (g : TreeAut d),
      (∀ w, (g.toEquiv w).1.length = w.1.length) →
      ∀ u v, u.1 <+: v.1 → (g.toEquiv u).1 <+: (g.toEquiv v).1 := by
    intro g hg u v huv
    have heq : u = ConnectedHull.takeVertex v u.1.length :=
      Subtype.ext (List.prefix_iff_eq_take.mp huv)
    have hm := congrArg g.toEquiv heq
    rw [map_takeVertex_of_length_preserving g hg] at hm
    rw [hm]
    exact List.take_prefix _ _
  constructor
  · intro h
    simpa only [TreeAut.symm, Equiv.symm_apply_apply] using
      forward g.symm (symm_length_eq g hg) (g.toEquiv u) (g.toEquiv v) h
  · exact forward g hg u v

end TreeAut

end Problem367

end OAI
