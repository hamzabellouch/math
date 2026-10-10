import OAI.NumberTheory.Ostmann.Construction.ExpandedScheduleHistory
import OAI.NumberTheory.Ostmann.Construction.WordRangeBounds

namespace OAI

/-! # Original atom-product and word-bin ranges on the expanded schedule -/

namespace Ostmann

open scoped Classical

structure ScheduleAtomRange {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) where
  atoms : List (CopyScheduleAtoms role n)
  lower : ℝ
  upper : ℝ

noncomputable def ScheduleAtomRange.Holds {I : Type*} {role : I → CopyScheduleRole} {n : ℕ}
    (r : ScheduleAtomRange role n) (x : CopyScheduleAtoms role n → ℕ) : Prop :=
  ((r.atoms.map x).prod : ℝ) ∈ Set.Icc r.lower r.upper

noncomputable def ScheduleAtomRange.toWord {I σ : Type*} {role : I → CopyScheduleRole} {n : ℕ}
    (r : ScheduleAtomRange role n) (current : CopyScheduleAtoms role n → List σ) : WordRange σ :=
  ⟨r.atoms.flatMap current, r.lower, r.upper⟩

theorem ScheduleAtomRange.toWord_holds {I σ : Type*} {role : I → CopyScheduleRole} {n : ℕ}
    (r : ScheduleAtomRange role n) (current : CopyScheduleAtoms role n → List σ) (x : σ → ℕ) :
    (r.toWord current).Holds x ↔ r.Holds (expandedAtomValues role n current x) := by
  unfold WordRange.Holds ScheduleAtomRange.Holds toWord
  rw [list_flatMap_product]
  rfl

theorem ScheduleAtomRange.toWord_length {I σ : Type*} {role : I → CopyScheduleRole} {n : ℕ}
    (r : ScheduleAtomRange role n) (current : CopyScheduleAtoms role n → List σ)
    (A M : ℕ) (hr : r.atoms.length ≤ A) (hc : ∀ i, (current i).length ≤ M) :
    (r.toWord current).word.length ≤ A * M := by
  exact (list_flatMap_length_bound r.atoms current M (fun i _ => hc i)).trans
    (Nat.mul_le_mul_right M hr)

noncomputable def expandedScheduleRanges {I σ : Type*} (role : I → CopyScheduleRole)
    (address : ℕ → List Bool → σ) (ranges : (n : ℕ) → List (ScheduleAtomRange role n)) :
    (n : ℕ) → List Bool → (CopyScheduleAtoms role n → List σ) → WordRangeDecoration σ n
  | 0, _, current => .leaf ((ranges 0).map fun r => r.toWord current)
  | n + 1, path, current => .node ((ranges (n + 1)).map fun r => r.toWord current)
      (expandedScheduleRanges role address ranges n (true :: path)
        (reverseCopyLabelMap role n true [address n path] current))
      (expandedScheduleRanges role address ranges n (false :: path)
        (reverseCopyLabelMap role n false [address n path] current))

/-- The range count is controlled at every stage, including the terminal bins. -/
theorem expandedScheduleRanges_count_bounded {I σ : Type*} (role : I → CopyScheduleRole)
    (address : ℕ → List Bool → σ) (ranges : (n : ℕ) → List (ScheduleAtomRange role n))
    (n K : ℕ) (hK : ∀ j ≤ n, (ranges j).length ≤ K)
    (path : List Bool) (current : CopyScheduleAtoms role n → List σ) :
    (expandedScheduleRanges role address ranges n path current).CountBounded K := by
  induction n generalizing path with
  | zero => simpa only [expandedScheduleRanges, WordRangeDecoration.CountBounded, List.length_map]
      using hK 0 le_rfl
  | succ n ih =>
    exact ⟨by simpa only [List.length_map] using hK (n + 1) le_rfl,
      ih (fun j hj => hK j (by omega)) _ _, ih (fun j hj => hK j (by omega)) _ _⟩

/-- Products in all original range tests have the same finite word bound
as their actual constituent expansion. -/
theorem expandedScheduleRanges_words_bounded {I σ : Type*} (role : I → CopyScheduleRole)
    (address : ℕ → List Bool → σ) (ranges : (n : ℕ) → List (ScheduleAtomRange role n))
    (n A M : ℕ) (hM : 1 ≤ M)
    (hA : ∀ j ≤ n, ∀ r ∈ ranges j, r.atoms.length ≤ A)
    (path : List Bool) (current : CopyScheduleAtoms role n → List σ)
    (hc : ∀ i, (current i).length ≤ M) :
    (expandedScheduleRanges role address ranges n path current).WordsBounded (A * M + 1) := by
  induction n generalizing path with
  | zero =>
    intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    exact Nat.add_le_add_right (q.toWord_length current A M (hA 0 le_rfl q hq) hc) 1
  | succ n ih =>
    refine ⟨?_, ih (fun j hj => hA j (by omega)) _ _
      (reverseCopyLabelMap_list_length role n true _ current M hM hc),
      ih (fun j hj => hA j (by omega)) _ _
      (reverseCopyLabelMap_list_length role n false _ current M hM hc)⟩
    intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    exact Nat.add_le_add_right (q.toWord_length current A M (hA (n + 1) le_rfl q hq) hc) 1

end Ostmann

end OAI
