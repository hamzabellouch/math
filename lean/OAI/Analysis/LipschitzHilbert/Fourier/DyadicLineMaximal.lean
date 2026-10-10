import OAI.Analysis.LipschitzHilbert.Fourier.DyadicLineNesting
import Mathlib.Data.Nat.Find

namespace OAI

/-! Maximal bad intervals exist below a fixed largest dyadic scale. -/

noncomputable section

open Set

namespace LipschitzHilbert.DyadicLineGrid

def MaximalBad (q top : ℤ) (bad : ℤ → ℤ → Prop) (k j : ℤ) : Prop :=
  k ≤ top ∧ bad k j ∧ ∀ l i, k < l → l ≤ top → cell q k j ⊆ cell q l i → ¬bad l i

/-- Every bad interval has a maximal bad ancestor before the prescribed
largest scale. No choice from an uncountable interval family is involved. -/
theorem exists_maximalBad {q top k j : ℤ} {bad : ℤ → ℤ → Prop}
    (hktop : k ≤ top) (hbad : bad k j) :
    ∃ l i, MaximalBad q top bad l i ∧ cell q k j ⊆ cell q l i := by
  classical
  obtain ⟨x, hx⟩ := cell_nonempty q k j
  obtain ⟨N, hN⟩ := Int.le.dest hktop
  let P : ℕ → Prop := fun n => bad (k + n) (index q (k + n) x)
  have hP0 : P 0 := by
    simpa only [P, Nat.cast_zero, add_zero, index_eq_of_mem hx] using hbad
  let n := Nat.findGreatest P N
  have hn : n ≤ N := Nat.findGreatest_le N
  have hPn : P n := Nat.findGreatest_spec (Nat.zero_le N) hP0
  have hkn : k ≤ k + (n : ℤ) := by omega
  have hntop : k + (n : ℤ) ≤ top := by omega
  refine ⟨k + n, index q (k + n) x, ⟨hntop, hPn, ?_⟩, cell_subset_index hkn hx⟩
  intro l i hnl hltop hsub hbi
  have hkl : k ≤ l := hkn.trans hnl.le
  obtain ⟨m, hm⟩ := Int.le.dest hkl
  have hmn : n < m := by omega
  have hmN : m ≤ N := by omega
  have hxi : x ∈ cell q l i := hsub (mem_index_cell q (k + n) x)
  have hmP : P m := by
    dsimp only [P]
    rw [hm, index_eq_of_mem hxi]
    exact hbi
  exact Nat.findGreatest_is_greatest hmn hmN hmP

/-- Within one bin, distinct maximal bad intervals are disjoint. -/
theorem maximalBad_disjoint {q top k l i j : ℤ} {bad : ℤ → ℤ → Prop}
    (hi : MaximalBad q top bad k i) (hj : MaximalBad q top bad l j)
    (hne : (k, i) ≠ (l, j)) : Disjoint (cell q k i) (cell q l j) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · exact hi.2.2 l j hkl hj.1 (cell_subset_of_intersect hkl.le ⟨x, hxi, hxj⟩) hj.2.1
  · subst l
    have hij : i = j := (index_eq_of_mem hxi).symm.trans (index_eq_of_mem hxj)
    exact hne (by simp [hij])
  · exact hj.2.2 k i hlk hi.1 (cell_subset_of_intersect hlk.le ⟨x, hxj, hxi⟩) hi.2.1

end LipschitzHilbert.DyadicLineGrid

end

end OAI
