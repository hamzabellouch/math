import OAI.Analysis.LipschitzHilbert.Trees.DyadicLineGrid

namespace OAI

/-! Arbitrary-depth nesting and uniqueness in the alternating line grids. -/

noncomputable section

open Set

namespace LipschitzHilbert.DyadicLineGrid

def ancestor (q k j : ℤ) : ℕ → ℤ
  | 0 => j
  | n + 1 => parent q (k + n) (ancestor q k j n)

theorem cell_subset_ancestor (q k j : ℤ) (n : ℕ) :
    cell q k j ⊆ cell q (k + n) (ancestor q k j n) := by
  induction n with
  | zero => simp [ancestor]
  | succ n ih =>
    have h := ih.trans (cell_subset_parent q (k + n) (ancestor q k j n))
    simpa only [ancestor, Nat.cast_add, Nat.cast_one, add_assoc] using h

theorem index_eq_of_mem {q k j : ℤ} {x : ℝ} (hx : x ∈ cell q k j) :
    index q k x = j := by
  by_contra hne
  exact Set.disjoint_left.mp (cells_disjoint q k hne) (mem_index_cell q k x) hx

theorem cell_nonempty (q k j : ℤ) : (cell q k j).Nonempty := by
  refine ⟨left q k j, le_rfl, ?_⟩
  unfold left
  have hs := scale_pos k
  push_cast
  nlinarith

/-- Intersecting cells at ordered scales are nested, including across
arbitrarily many generations. -/
theorem cell_subset_of_intersect {q k l i j : ℤ} (hkl : k ≤ l)
    (hij : (cell q k i ∩ cell q l j).Nonempty) :
    cell q k i ⊆ cell q l j := by
  obtain ⟨n, rfl⟩ := Int.le.dest hkl
  have hsub := cell_subset_ancestor q k i n
  obtain ⟨x, hxi, hxj⟩ := hij
  have heq : ancestor q k i n = j := by
    by_contra hne
    exact Set.disjoint_left.mp (cells_disjoint q (k + n) hne) (hsub hxi) hxj
  simpa only [heq] using hsub

theorem cell_subset_index {q k l j : ℤ} {x : ℝ} (hkl : k ≤ l)
    (hx : x ∈ cell q k j) : cell q k j ⊆ cell q l (index q l x) :=
  cell_subset_of_intersect hkl ⟨x, hx, mem_index_cell q l x⟩

theorem cells_nested_or_disjoint (q k l i j : ℤ) :
    cell q k i ⊆ cell q l j ∨ cell q l j ⊆ cell q k i ∨
      Disjoint (cell q k i) (cell q l j) := by
  by_cases h : (cell q k i ∩ cell q l j).Nonempty
  · rcases le_total k l with hkl | hlk
    · exact Or.inl (cell_subset_of_intersect hkl h)
    · exact Or.inr (Or.inl (cell_subset_of_intersect hlk (by simpa only [inter_comm] using h)))
  · exact Or.inr (Or.inr (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h)))

end LipschitzHilbert.DyadicLineGrid

end

end OAI
