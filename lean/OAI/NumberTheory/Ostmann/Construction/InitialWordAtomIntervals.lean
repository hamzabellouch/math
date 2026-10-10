import OAI.NumberTheory.Ostmann.Construction.InitialWordBinIdentification
import OAI.NumberTheory.Ostmann.Arithmetic.AtomIntervalRanges

namespace OAI

/-! # Whole-atom intervals retain exactly the selected initial word bin -/
namespace Ostmann
open scoped BigOperators Classical

noncomputable def initialWordAtomLower {C : Type*} (j : ℕ) (lo : C → ℕ)
    (v : Bool × Option C) : ℕ :=
  v.2.elim ⌈Real.exp (j : ℝ)⌉₊ lo

noncomputable def initialWordAtomUpper {C : Type*} (j : ℕ) (hi : C → ℕ)
    (v : Bool × Option C) : ℕ :=
  v.2.elim (⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1) hi

theorem initialWordBinRange_values {C : Type*}
    (role : Bool × Option C → CopyScheduleRole) (b : Bool) (j : ℕ)
    (x : CopyScheduleAtoms role 0 → ℕ) :
    (initialWordBinRange role b j).Holds x ↔
      ⌈Real.exp (j : ℝ)⌉₊ ≤ x ⟨(b, none), trivial⟩ ∧
      x ⟨(b, none), trivial⟩ ≤ ⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 := by
  simp only [initialWordBinRange, ScheduleAtomRange.Holds, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, Set.mem_Icc, Nat.cast_le]

theorem initialWordBinRanges_values {C : Type*}
    (role : Bool × Option C → CopyScheduleRole) (j : ℕ)
    (x : CopyScheduleAtoms role 0 → ℕ) :
    (∀ r ∈ initialWordBinRanges role j, r.Holds x) ↔
      ∀ b : Bool, ⌈Real.exp (j : ℝ)⌉₊ ≤ x ⟨(b, none), trivial⟩ ∧
        x ⟨(b, none), trivial⟩ ≤ ⌈Real.exp ((j : ℝ) + 1)⌉₊ - 1 := by
  simp only [initialWordBinRanges, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, initialWordBinRange_values]
  constructor
  · rintro ⟨ht, hf⟩ b
    cases b
    · exact hf
    · exact ht
  · intro h
    exact ⟨h true, h false⟩

/-- All nonword intervals already hold on the original prior. Thus adding
these guards leaves precisely the two original word-bin events. -/
theorem initialWordAtomIntervals_equiv {C : Type*} [Fintype C]
    (role : Bool × Option C → CopyScheduleRole) (j : ℕ) (lo hi : C → ℕ)
    (x : CopyScheduleAtoms role 0 → ℕ)
    (hcell : ∀ (b : Bool) (c : C), lo c ≤ x ⟨(b, some c), trivial⟩ ∧
      x ⟨(b, some c), trivial⟩ ≤ hi c) :
    (∀ r ∈ atomIntervalRanges role (initialWordAtomLower j lo)
      (initialWordAtomUpper j hi) 0, r.Holds x) ↔
    ∀ r ∈ initialWordBinRanges role j, r.Holds x := by
  rw [atomIntervalRanges_holds_iff, initialWordBinRanges_values]
  constructor
  · intro h b
    exact h ⟨(b, none), trivial⟩
  · intro h v
    rcases v with ⟨⟨b, c⟩, hv⟩
    cases c with
    | none => exact h b
    | some c => exact hcell b c

end Ostmann

end OAI
