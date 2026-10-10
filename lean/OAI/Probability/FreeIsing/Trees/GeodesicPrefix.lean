import OAI.Probability.FreeIsing.Trees.PathPrefix

namespace OAI

namespace Problem367.TreePath

theorem length_eq_index_of_nonbacktracking {d N : ℕ}
    (p : ℕ → TreeVertex d)
    (hroot : p 0 = ConnectedHull.root d)
    (hadj : ∀ i < N, treeAdj (p i) (p (i + 1)))
    (hback : ∀ i, i + 2 ≤ N → p (i + 2) ≠ p i) :
    ∀ i ≤ N, (p i).1.length = i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi
      cases i with
      | zero => rw [hroot]; rfl
      | succ i =>
          have hprev := ih i (by omega) (by omega)
          rcases treeAdj_length (hadj i (by omega)) with hforward | hreverse
          · omega
          · cases i with
            | zero => omega
            | succ j =>
                change (p (j + 1)).1.length = j + 1 at hprev
                change (p (j + 1)).1.length = (p (j + 2)).1.length + 1 at hreverse
                have hj := ih j (by omega) (by omega)
                have hrev : treeAdj (p (j + 2)) (p (j + 1)) :=
                  (hadj (j + 1) (by omega)).symm
                have heq : p (j + 2) = p j :=
                  treeAdj_lower_unique hrev (hadj j (by omega))
                    (by omega) (by omega)
                exact False.elim (hback j (by omega) heq)

theorem eq_takeVertex_of_nonbacktracking {d N : ℕ}
    (p : ℕ → TreeVertex d)
    (hroot : p 0 = ConnectedHull.root d)
    (hadj : ∀ i < N, treeAdj (p i) (p (i + 1)))
    (hback : ∀ i, i + 2 ≤ N → p (i + 2) ≠ p i) :
    ∀ i ≤ N, p i = ConnectedHull.takeVertex (p N) i := by
  have hlen := length_eq_index_of_nonbacktracking p hroot hadj hback
  intro i hi
  induction hi using Nat.decreasingInduction with
  | self =>
      have h := ConnectedHull.prefix_length (p N)
      rw [hlen N (Nat.le_refl N)] at h
      exact h.symm
  | of_succ k hk ih =>
      apply treeAdj_lower_unique (hadj k hk)
      · rw [ih]
        apply ConnectedHull.prefix_adj
        rw [hlen N (Nat.le_refl N)]
        exact hk
      · rw [hlen k (by omega), hlen (k + 1) (by omega)]
        omega
      · rw [hlen (k + 1) (by omega)]
        simp only [ConnectedHull.takeVertex, List.length_take, hlen N (Nat.le_refl N)]
        omega

theorem exists_treeAut_map_nonbacktracking_to_prefix {d N : ℕ}
    (p : ℕ → TreeVertex d)
    (hadj : ∀ i < N, treeAdj (p i) (p (i + 1)))
    (hback : ∀ i, i + 2 ≤ N → p (i + 2) ≠ p i) :
    ∃ g : TreeAut d, (g.toEquiv (p N)).1.length = N ∧
      ∀ i ≤ N, g.toEquiv (p i) = ConnectedHull.takeVertex (g.toEquiv (p N)) i := by
  obtain ⟨g, hg⟩ := exists_treeAut_to_root (p 0)
  let q : ℕ → TreeVertex d := fun i => g.toEquiv (p i)
  have hroot : q 0 = ConnectedHull.root d := hg
  have hqadj : ∀ i < N, treeAdj (q i) (q (i + 1)) :=
    fun i hi => (g.map_adj _ _).mpr (hadj i hi)
  have hqback : ∀ i, i + 2 ≤ N → q (i + 2) ≠ q i := by
    intro i hi heq
    exact hback i hi (g.toEquiv.injective heq)
  exact ⟨g, length_eq_index_of_nonbacktracking q hroot hqadj hqback N (Nat.le_refl N),
    eq_takeVertex_of_nonbacktracking q hroot hqadj hqback⟩

theorem exists_treeAut_map_simple_to_prefix {d N : ℕ}
    (p : ℕ → TreeVertex d)
    (hadj : ∀ i < N, treeAdj (p i) (p (i + 1)))
    (hinj : Set.InjOn p (Set.Iic N)) :
    ∃ g : TreeAut d, (g.toEquiv (p N)).1.length = N ∧
      ∀ i ≤ N, g.toEquiv (p i) = ConnectedHull.takeVertex (g.toEquiv (p N)) i := by
  apply exists_treeAut_map_nonbacktracking_to_prefix p hadj
  intro i hi heq
  have : i + 2 = i := hinj hi (by simpa only [Set.mem_Iic] using (by omega : i ≤ N)) heq
  omega

end Problem367.TreePath

end OAI
