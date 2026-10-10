import OAI.Probability.FreeIsing.Trees.ConnectedHull
import OAI.Probability.FreeIsing.Trees.Transitivity

namespace OAI

noncomputable section

namespace Problem367

def stripPrefixAut {d : ℕ} : List (Fin d) → TreeAut d
  | [] => TreeAut.refl d
  | a :: w => (prefixTreeAut a).trans (stripPrefixAut w)

theorem stripPrefixAut_of_append {d : ℕ} (stem : List (Fin d))
    (v : TreeVertex d) (s : List (Fin d)) (hv : v.1 = stem ++ s) :
    ((stripPrefixAut stem).toEquiv v).1 = s := by
  induction stem generalizing v with
  | nil =>
    change v.1 = s
    simpa only [List.nil_append] using hv
  | cons a stem ih =>
    change ((stripPrefixAut stem).toEquiv (prefixFlip a v)).1 = s
    apply ih
    simp [prefixFlip, prefixFlipWord, hv]

theorem stripPrefixAut_eq_drop {d : ℕ} (stem : List (Fin d))
    (v : TreeVertex d) (hpre : stem <+: v.1) :
    ((stripPrefixAut stem).toEquiv v).1 = v.1.drop stem.length := by
  obtain ⟨s, hs⟩ := hpre
  rw [stripPrefixAut_of_append stem v s hs.symm, ← hs]
  simp

def dropVertex {d : ℕ} (v : TreeVertex d) (i : ℕ) : TreeVertex d :=
  ⟨v.1.drop i, v.2.drop i⟩

@[simp] theorem dropVertex_val {d : ℕ} (v : TreeVertex d) (i : ℕ) :
    (dropVertex v i).1 = v.1.drop i := rfl

@[simp] theorem dropVertex_length {d : ℕ} (v : TreeVertex d) (i : ℕ) :
    (dropVertex v i).1.length = v.1.length - i := by simp

theorem stripPrefixAut_takeVertex {d : ℕ} (v : TreeVertex d)
    {i j : ℕ} (hi : i ≤ v.1.length) (hij : i ≤ j) :
    (stripPrefixAut (v.1.take i)).toEquiv (ConnectedHull.takeVertex v j) =
      ConnectedHull.takeVertex (dropVertex v i) (j - i) := by
  apply Subtype.ext
  have hpre : v.1.take i <+: (ConnectedHull.takeVertex v j).1 := by
    change v.1.take i <+: v.1.take j
    simpa only [List.take_take, Nat.min_eq_left hij] using
      List.take_prefix i (v.1.take j)
  rw [stripPrefixAut_eq_drop _ _ hpre]
  simp only [ConnectedHull.takeVertex, dropVertex, List.length_take,
    Nat.min_eq_left hi, List.drop_take]

theorem stripPrefixAut_takeVertex_self {d : ℕ} (v : TreeVertex d)
    {i : ℕ} (hi : i ≤ v.1.length) :
    (stripPrefixAut (v.1.take i)).toEquiv (ConnectedHull.takeVertex v i) =
      ConnectedHull.root d := by
  rw [stripPrefixAut_takeVertex v hi le_rfl]
  simp

theorem exists_treeAut_reroot_subsegment {d : ℕ} (v : TreeVertex d)
    {i j : ℕ} (hij : i ≤ j) (hj : j < v.1.length) :
    ∃ (w : TreeVertex d) (g : TreeAut d),
      w.1.length = j - i + 1 ∧
      ∀ k : ℕ, i ≤ k → k ≤ j + 1 →
        g.toEquiv (ConnectedHull.takeVertex v k) =
          ConnectedHull.takeVertex w (k - i) := by
  let w := ConnectedHull.takeVertex (dropVertex v i) (j - i + 1)
  refine ⟨w, stripPrefixAut (v.1.take i), ?_, ?_⟩
  · have hle : j - i + 1 ≤ v.1.length - i := by omega
    simp only [w, ConnectedHull.takeVertex, dropVertex, List.length_take,
      List.length_drop, Nat.min_eq_left hle]
  · intro k hik hkj
    rw [stripPrefixAut_takeVertex v (by omega) hik]
    apply Subtype.ext
    change (v.1.drop i).take (k - i) =
      ((v.1.drop i).take (j - i + 1)).take (k - i)
    rw [List.take_take, Nat.min_eq_left (by omega : k - i ≤ j - i + 1)]

theorem exists_treeAut_reroot_edge_pair {d : ℕ} (v : TreeVertex d)
    {i j : ℕ} (hij : i ≤ j) (hj : j < v.1.length) :
    ∃ (w : TreeVertex d) (g : TreeAut d),
      w.1.length = j - i + 1 ∧
      g.toEquiv (ConnectedHull.takeVertex v i) = ConnectedHull.root d ∧
      g.toEquiv (ConnectedHull.takeVertex v (i + 1)) = ConnectedHull.takeVertex w 1 ∧
      g.toEquiv (ConnectedHull.takeVertex v j) = ConnectedHull.takeVertex w (j - i) ∧
      g.toEquiv (ConnectedHull.takeVertex v (j + 1)) = w := by
  obtain ⟨w, g, hlen, hmap⟩ := exists_treeAut_reroot_subsegment v hij hj
  refine ⟨w, g, hlen, ?_, ?_, hmap j hij (by omega), ?_⟩
  · simpa using hmap i le_rfl (by omega)
  · simpa using hmap (i + 1) (by omega) (by omega)
  · have h := hmap (j + 1) (by omega) le_rfl
    have hk : j + 1 - i = w.1.length := by omega
    rw [hk, ConnectedHull.prefix_length] at h
    exact h

end Problem367

end

end OAI
