import OAI.NumberTheory.Ostmann.Construction.ScheduledTemplateBounds

namespace OAI

/-! # A finite, concrete variable set for the reverse atom construction -/

namespace Ostmann

open scoped Classical

/-- Actual surviving atoms and a finite supply of labelled pivot positions.
Unused pivot positions have no sampling prior. -/
abbrev ScheduledVariable {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :=
  CopyScheduleAtoms role n ⊕ (Fin (n + 1) × (Fin n → Bool))

noncomputable instance scheduledVariableFintype {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) : Fintype (ScheduledVariable role n) :=
  inferInstanceAs (Fintype (CopyScheduleAtoms role n ⊕ (Fin (n + 1) × (Fin n → Bool))))

def scheduledPivotAddress {I : Type*} (role : I → CopyScheduleRole) (n j : ℕ)
    (path : List Bool) : ScheduledVariable role n :=
  .inr (⟨j % (n + 1), Nat.mod_lt _ (by omega)⟩, fun i => path.getD i.val false)

noncomputable def finiteScheduledTemplate {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ) (n : ℕ) :
    WordTransferTemplate (ScheduledVariable role n) n :=
  scheduledWordTemplate role (scheduledPivotAddress role n) childBound pivotBound n [] Sum.inl

def scheduledPrimeAssignment {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (a : CopyScheduleAtoms role n → ℕ) : ScheduledVariable role n → ℕ :=
  Sum.elim a (fun _ => 1)

theorem scheduledPivotAddress_ne_actual {I : Type*} (role : I → CopyScheduleRole)
    (n j : ℕ) (path : List Bool) (i : CopyScheduleAtoms role n) :
    scheduledPivotAddress role n j path ≠ Sum.inl i := by
  simp only [scheduledPivotAddress, ne_eq, reduceCtorEq, not_false_eq_true]

theorem scheduledPivotAddress_level {I : Type*} (role : I → CopyScheduleRole)
    (n j k : ℕ) (hj : j < n + 1) (hk : k < n + 1) (path path' : List Bool)
    (he : scheduledPivotAddress role n j path = scheduledPivotAddress role n k path') : j = k := by
  have hh := congrArg (fun q : Fin (n + 1) × (Fin n → Bool) => q.1.val) (Sum.inr.inj he)
  simpa only [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hk] using hh

theorem scheduledPivotAddress_path {I : Type*} (role : I → CopyScheduleRole)
    (n j : ℕ) (path path' : List Bool) (hlen : path.length = path'.length)
    (hbound : path.length ≤ n)
    (he : scheduledPivotAddress role n j path = scheduledPivotAddress role n j path') : path = path' := by
  have hh := congrArg (fun q : Fin (n + 1) × (Fin n → Bool) => q.2) (Sum.inr.inj he)
  apply List.ext_getElem hlen
  intro i hi hi'
  have hiN : i < n := lt_of_lt_of_le hi hbound
  have hv := congrFun hh ⟨i, hiN⟩
  simpa only [List.getD_eq_getElem path false hi, List.getD_eq_getElem path' false hi'] using hv

theorem finiteScheduledTemplate_size {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ) (n : ℕ) :
    (finiteScheduledTemplate role childBound pivotBound n).WordsBounded (scheduledTemplateWordBound I n) :=
  scheduledWordTemplate_size role (scheduledPivotAddress role n) childBound pivotBound n [] Sum.inl

theorem scheduledVariable_card_le {I : Type*} [Fintype I] (role : I → CopyScheduleRole) (n : ℕ) :
    Fintype.card (ScheduledVariable role n) ≤ 3 ^ n * Fintype.card I + (n + 1) * 2 ^ n := by
  have ha : Fintype.card (CopyScheduleAtoms role n) ≤ 3 ^ n * Fintype.card I := by
    rw [← copyScheduleVertex_card n]
    exact Fintype.card_subtype_le _
  change Fintype.card (CopyScheduleAtoms role n ⊕ (Fin (n + 1) × (Fin n → Bool))) ≤ _
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, Fintype.card_bool]
  omega

end Ostmann

end OAI
