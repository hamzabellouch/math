import OAI.Probability.FreeIsing.Trees.GeodesicPrefix
import OAI.Probability.FreeIsing.Trees.RootedTransitivity

namespace OAI

namespace Problem367

theorem exists_treeAut_map_all_prefixes {d : ℕ} (u v : TreeVertex d)
    (hlen : u.1.length = v.1.length) :
    ∃ g : TreeAut d, g.toEquiv (ConnectedHull.root d) = ConnectedHull.root d ∧
      ∀ n, g.toEquiv (ConnectedHull.takeVertex u n) = ConnectedHull.takeVertex v n := by
  obtain ⟨g, huv, hg⟩ := exists_rootFixing_treeAut_map u v hlen
  refine ⟨g, hg, fun n => ?_⟩
  rw [g.map_takeVertex_of_root_eq hg, huv]

namespace TreePath

theorem exists_treeAut_map_nonbacktracking_paths {d N : ℕ}
    (p q : ℕ → TreeVertex d)
    (hp : ∀ i < N, treeAdj (p i) (p (i + 1)))
    (hpback : ∀ i, i + 2 ≤ N → p (i + 2) ≠ p i)
    (hq : ∀ i < N, treeAdj (q i) (q (i + 1)))
    (hqback : ∀ i, i + 2 ≤ N → q (i + 2) ≠ q i) :
    ∃ g : TreeAut d, ∀ i ≤ N, g.toEquiv (p i) = q i := by
  obtain ⟨g, hglen, hg⟩ := exists_treeAut_map_nonbacktracking_to_prefix p hp hpback
  obtain ⟨h, hhlen, hh⟩ := exists_treeAut_map_nonbacktracking_to_prefix q hq hqback
  obtain ⟨k, _, hk⟩ := exists_treeAut_map_all_prefixes
    (g.toEquiv (p N)) (h.toEquiv (q N)) (hglen.trans hhlen.symm)
  refine ⟨(g.trans k).trans h.symm, fun i hi => ?_⟩
  change h.toEquiv.symm (k.toEquiv (g.toEquiv (p i))) = q i
  rw [hg i hi, hk i, ← hh i hi, Equiv.symm_apply_apply]

theorem exists_treeAut_map_simple_paths {d N : ℕ}
    (p q : ℕ → TreeVertex d)
    (hp : ∀ i < N, treeAdj (p i) (p (i + 1)))
    (hpinj : Set.InjOn p (Set.Iic N))
    (hq : ∀ i < N, treeAdj (q i) (q (i + 1)))
    (hqinj : Set.InjOn q (Set.Iic N)) :
    ∃ g : TreeAut d, ∀ i ≤ N, g.toEquiv (p i) = q i := by
  refine exists_treeAut_map_nonbacktracking_paths p q hp ?_ hq ?_
  · intro i hi heq
    have : i + 2 = i := hpinj hi (by simpa only [Set.mem_Iic] using (by omega : i ≤ N)) heq
    omega
  · intro i hi heq
    have : i + 2 = i := hqinj hi (by simpa only [Set.mem_Iic] using (by omega : i ≤ N)) heq
    omega

theorem exists_treeAut_map_fin_simple_paths {d N : ℕ}
    (p q : Fin (N + 1) → TreeVertex d)
    (hp : ∀ i : Fin N, treeAdj (p i.castSucc) (p i.succ))
    (hpinj : Function.Injective p)
    (hq : ∀ i : Fin N, treeAdj (q i.castSucc) (q i.succ))
    (hqinj : Function.Injective q) :
    ∃ g : TreeAut d, ∀ i, g.toEquiv (p i) = q i := by
  let index (i : ℕ) : Fin (N + 1) := ⟨min i N, Nat.lt_succ_of_le (Nat.min_le_right i N)⟩
  have index_val (i : ℕ) (hi : i ≤ N) : (index i).val = i := Nat.min_eq_left hi
  have index_cast (i : Fin N) : index i = i.castSucc := by
    apply Fin.ext
    exact index_val i (Nat.le_of_lt i.isLt)
  have index_succ (i : Fin N) : index (i + 1) = i.succ := by
    apply Fin.ext
    exact index_val (i + 1) (Nat.succ_le_of_lt i.isLt)
  have index_inj : Set.InjOn index (Set.Iic N) := by
    intro i hi j hj heq
    have h := congrArg Fin.val heq
    simpa only [index_val i hi, index_val j hj] using h
  have padj : ∀ i < N, treeAdj (p (index i)) (p (index (i + 1))) := by
    intro i hi
    rw [index_cast ⟨i, hi⟩, index_succ ⟨i, hi⟩]
    exact hp ⟨i, hi⟩
  have qadj : ∀ i < N, treeAdj (q (index i)) (q (index (i + 1))) := by
    intro i hi
    rw [index_cast ⟨i, hi⟩, index_succ ⟨i, hi⟩]
    exact hq ⟨i, hi⟩
  obtain ⟨g, hg⟩ := exists_treeAut_map_simple_paths (p ∘ index) (q ∘ index)
    padj (fun _ hi _ hj heq => index_inj hi hj (hpinj heq))
    qadj (fun _ hi _ hj heq => index_inj hi hj (hqinj heq))
  refine ⟨g, fun i => ?_⟩
  have hi : index i = i := Fin.ext (index_val i (Nat.le_of_lt_succ i.isLt))
  simpa only [Function.comp_apply, hi] using hg i (Nat.le_of_lt_succ i.isLt)

end TreePath

end Problem367

end OAI
