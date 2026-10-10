import OAI.NumberTheory.Ostmann.Construction.ExpandedUnitReplay
import OAI.NumberTheory.Ostmann.Construction.ExpandedRangedWeight

namespace OAI

/-! # The actual unit condition on every current atom at every frequency -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def totalAtomUnitRanges {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) : List (ScheduleAtomRange role n) :=
  [⟨Finset.univ.toList, 0, 0⟩]

/-- A unit product is exactly the original assertion that every current
atom is a unit. The dummy interval endpoints play no part in this test. -/
theorem totalAtomUnitRanges_iff {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (s : ℤ) :
    (∀ r ∈ totalAtomUnitRanges role n, ((r.atoms.map x).prod).Coprime s.natAbs) ↔
      ∀ i, (x i).Coprime s.natAbs := by
  simp only [totalAtomUnitRanges, List.mem_singleton, forall_eq]
  rw [Finset.prod_map_toList]
  exact Nat.coprime_fintype_prod_left_iff

theorem WordRangeDecoration.wordsBounded_mono {σ : Type*} {n B C : ℕ}
    (D : WordRangeDecoration σ n) (hD : D.WordsBounded B) (hBC : B ≤ C) : D.WordsBounded C := by
  induction D with
  | leaf ranges => exact fun r hr => (hD r hr).trans hBC
  | node ranges L R ihL ihR => exact ⟨fun r hr => (hD.1 r hr).trans hBC, ihL hD.2.1, ihR hD.2.2⟩

theorem copyScheduleAtoms_card_le {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) :
    Fintype.card (CopyScheduleAtoms role n) ≤ 3 ^ n * Fintype.card I := by
  rw [← copyScheduleVertex_card n]
  exact Fintype.card_subtype_le _

/-- The complete inherited unit family has at most one test per tree node. -/
theorem totalAtomUnits_count {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V) :
    (expandedRootRanges role n words (totalAtomUnitRanges role)).count ≤ 2 ^ (n + 1) - 1 := by
  have h := expandedScheduleRanges_count_bounded role (expandedPivotAddress V n)
    (totalAtomUnitRanges role) n 1 (fun _ _ => by simp [totalAtomUnitRanges]) []
    (fun i => (words i).map Sum.inl)
  simpa only [Nat.one_mul, expandedRootRanges] using WordRangeDecoration.count_le _ 1 h

/-- Its product words fit the same concrete bound as the Fourier template. -/
theorem totalAtomUnits_words_bounded {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (M : ℕ) (hM : 1 ≤ M) (hwords : ∀ i, (words i).length ≤ M) :
    (expandedRootRanges role n words (totalAtomUnitRanges role)).WordsBounded
      (2 * 3 ^ n * Fintype.card I * M + 4) := by
  have hA : ∀ j ≤ n, ∀ r ∈ totalAtomUnitRanges role j,
      r.atoms.length ≤ 3 ^ n * Fintype.card I := by
    intro j hj r hr
    have he : r = ⟨Finset.univ.toList, 0, 0⟩ := List.mem_singleton.mp hr
    subst r
    simp only [Finset.length_toList, Finset.card_univ]
    exact (copyScheduleAtoms_card_le role j).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hj))
  have hh := expandedScheduleRanges_words_bounded role (expandedPivotAddress V n)
    (totalAtomUnitRanges role) n (3 ^ n * Fintype.card I) M hM hA []
    (fun i => (words i).map Sum.inl) (fun i => by simpa only [List.length_map] using hwords i)
  exact WordRangeDecoration.wordsBounded_mono _ hh (by nlinarith only [Nat.zero_le (3 ^ n * Fintype.card I * M)])

end Ostmann

end OAI
