import OAI.NumberTheory.TwoPoint.Circuits.CircuitRestriction

namespace OAI

/-! Partial assignments and the consistent terms used in the canonical
decision tree of a DNF. Each term contains at most one literal per variable. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

abbrev PartialAssignment (n : ℕ) := Fin n → Option Bool

namespace PartialAssignment

def apply {n : ℕ} (ρ : PartialAssignment n) (x : BooleanCube n) : BooleanCube n :=
  fun i => (ρ i).getD (x i)

def Extends {n : ℕ} (ρ τ : PartialAssignment n) : Prop :=
  ∀ i b, ρ i = some b → τ i = some b

def assign {n : ℕ} (ρ : PartialAssignment n) (S : Finset (Fin n))
    (x : BooleanCube n) : PartialAssignment n := fun i => if i ∈ S then some (x i) else ρ i

def free {n : ℕ} (ρ : PartialAssignment n) : Finset (Fin n) :=
  univ.filter (fun i => ρ i = none)

@[simp] lemma assign_empty {n : ℕ} (ρ : PartialAssignment n) (x : BooleanCube n) :
    ρ.assign ∅ x = ρ := by funext i; simp [assign]

lemma assign_insert {n : ℕ} (ρ : PartialAssignment n) (S : Finset (Fin n))
    (x : BooleanCube n) (i : Fin n) :
    ρ.assign (insert i S) x = assign (Function.update ρ i (some (x i))) S x := by
  funext j
  by_cases hji : j = i <;> by_cases hj : j ∈ S <;> simp [assign, hji, hj]

lemma apply_assign_free {n : ℕ} (ρ : PartialAssignment n) (S : Finset (Fin n))
    (hS : S ⊆ ρ.free) (x : BooleanCube n) :
    (ρ.assign S x).apply x = ρ.apply x := by
  funext i
  by_cases hi : i ∈ S
  · have hρ : ρ i = none := (mem_filter.mp (hS hi)).2
    simp [assign, apply, hi, hρ]
  · simp [assign, apply, hi]

lemma assign_extends {n : ℕ} (ρ : PartialAssignment n) (S : Finset (Fin n))
    (hS : S ⊆ ρ.free) (x : BooleanCube n) : ρ.Extends (ρ.assign S x) := by
  intro i b hb
  have hi : i ∉ S := by
    intro hi
    have hn := (mem_filter.mp (hS hi)).2
    rw [hb] at hn
    cases hn
  simp [assign, hi, hb]

lemma extends_trans {n : ℕ} {ρ σ τ : PartialAssignment n}
    (hρσ : ρ.Extends σ) (hστ : σ.Extends τ) : ρ.Extends τ :=
  fun i b hb => hστ i b (hρσ i b hb)

end PartialAssignment

structure CubeTerm (n : ℕ) where
  support : Finset (Fin n)
  value : BooleanCube n

namespace CubeTerm

def eval {n : ℕ} (C : CubeTerm n) (x : BooleanCube n) : Bool :=
  decide (∀ i ∈ C.support, x i = C.value i)

def Compatible {n : ℕ} (C : CubeTerm n) (ρ : PartialAssignment n) : Prop :=
  ∀ i ∈ C.support, ρ i = none ∨ ρ i = some (C.value i)

def Satisfied {n : ℕ} (C : CubeTerm n) (ρ : PartialAssignment n) : Prop :=
  ∀ i ∈ C.support, ρ i = some (C.value i)

def live {n : ℕ} (C : CubeTerm n) (ρ : PartialAssignment n) : Finset (Fin n) :=
  C.support.filter (fun i => ρ i = none)

lemma live_subset_free {n : ℕ} (C : CubeTerm n) (ρ : PartialAssignment n) :
    C.live ρ ⊆ ρ.free := by
  intro i hi
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩

lemma incompatible_mono {n : ℕ} (C : CubeTerm n) {ρ τ : PartialAssignment n}
    (hρ : ¬ C.Compatible ρ) (h : ρ.Extends τ) : ¬ C.Compatible τ := by
  intro hτ
  apply hρ
  intro i hi
  cases hri : ρ i with
  | none => exact Or.inl rfl
  | some b =>
    have hti := h i b hri
    rcases hτ i hi with hn | hv
    · rw [hti] at hn
      cases hn
    · have hb : b = C.value i := Option.some.inj (hti.symm.trans hv)
      exact Or.inr (congrArg some hb)

lemma eval_apply_of_incompatible {n : ℕ} (C : CubeTerm n)
    (ρ : PartialAssignment n) (hρ : ¬ C.Compatible ρ) (x : BooleanCube n) :
    C.eval (ρ.apply x) = false := by
  apply Bool.eq_false_iff.mpr
  intro he
  apply hρ
  have he : ∀ i ∈ C.support, ρ.apply x i = C.value i := of_decide_eq_true he
  intro i hi
  cases hr : ρ i with
  | none => exact Or.inl rfl
  | some b =>
    right
    have hb := he i hi
    simpa [PartialAssignment.apply, hr] using hb

lemma satisfied_assign_live_iff {n : ℕ} (C : CubeTerm n)
    (ρ : PartialAssignment n) (hρ : C.Compatible ρ) (x : BooleanCube n) :
    C.Satisfied (ρ.assign (C.live ρ) x) ↔ C.eval (ρ.apply x) = true := by
  simp only [Satisfied, eval, decide_eq_true_eq]
  constructor
  · intro hs i hi
    by_cases hl : i ∈ C.live ρ
    · have hn := (mem_filter.mp hl).2
      have hb := hs i hi
      simpa [PartialAssignment.assign, PartialAssignment.apply, hl, hn] using hb
    · have hn : ρ i ≠ none := fun hn => hl (mem_filter.mpr ⟨hi, hn⟩)
      have hv := (hρ i hi).resolve_left hn
      simp [PartialAssignment.apply, hv]
  · intro hx i hi
    by_cases hn : ρ i = none
    · have hl : i ∈ C.live ρ := mem_filter.mpr ⟨hi, hn⟩
      have hv := hx i hi
      simpa [PartialAssignment.assign, PartialAssignment.apply, hl, hn] using hv
    · have hl : i ∉ C.live ρ := fun hl => hn (mem_filter.mp hl).2
      simp [PartialAssignment.assign, hl, (hρ i hi).resolve_left hn]

lemma satisfied_assign_value {n : ℕ} (C : CubeTerm n)
    (ρ : PartialAssignment n) (hρ : C.Compatible ρ) :
    C.Satisfied (ρ.assign (C.live ρ) C.value) := by
  rw [C.satisfied_assign_live_iff ρ hρ]
  apply decide_eq_true
  intro i hi
  rcases hρ i hi with hn | hv
  · simp [PartialAssignment.apply, hn]
  · simp [PartialAssignment.apply, hv]

end CubeTerm

end TwoPointCorrelations

end OAI
