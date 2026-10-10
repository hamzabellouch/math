import OAI.NumberTheory.TwoPoint.Walks.ColumnRepresentatives
import OAI.NumberTheory.TwoPoint.Walks.ColumnRunEncoding

namespace OAI

/-! Canonical names distinguish precisely the original column's label classes. -/

namespace TwoPointCorrelations

open Finset

variable {α : Type*} [DecidableEq α] {N : ℕ}

def perfectColumnName : ℕ ⊕ ℕ → CanonicalColumnLabel
  | .inl a => .regular a
  | .inr a => .omitted a

lemma perfectColumnName_injective : Function.Injective perfectColumnName := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

lemma perfectColumnName_ne_fresh (a : ℕ ⊕ ℕ) (j : ℕ) :
    perfectColumnName a ≠ .freshImperfect j := by
  cases a <;> simp [perfectColumnName]

/-- Perfect classes keep their forest/omitted name. Classes with no perfect
occurrence use the index of their first occurrence. -/
def canonicalColumnName (label : Fin N → α) (perfect : Finset (Fin N))
    (name : Fin N → ℕ ⊕ ℕ) (i : Fin N) : CanonicalColumnLabel :=
  let j := columnRepresentative label perfect i
  if j ∈ perfect then perfectColumnName (name j) else .freshImperfect j.val

lemma canonicalColumnName_of_label_eq (label : Fin N → α) (perfect : Finset (Fin N))
    (name : Fin N → ℕ ⊕ ℕ) {i j : Fin N} (h : label i = label j) :
    canonicalColumnName label perfect name i = canonicalColumnName label perfect name j := by
  have hr := (columnRepresentative_eq_iff label perfect i j).mpr h
  simp only [canonicalColumnName, hr]

/-- The only needed naming hypothesis concerns the perfect occurrences.
Fresh imperfect classes are separated by their canonical references. -/
theorem canonicalColumnName_eq_iff (label : Fin N → α) (perfect : Finset (Fin N))
    (name : Fin N → ℕ ⊕ ℕ)
    (hname : ∀ i ∈ perfect, ∀ j ∈ perfect, name i = name j ↔ label i = label j)
    (i j : Fin N) :
    canonicalColumnName label perfect name i = canonicalColumnName label perfect name j ↔
      label i = label j := by
  constructor
  · intro heq
    let ri := columnRepresentative label perfect i
    let rj := columnRepresentative label perfect j
    change (if ri ∈ perfect then perfectColumnName (name ri) else .freshImperfect ri.val) =
      (if rj ∈ perfect then perfectColumnName (name rj) else .freshImperfect rj.val) at heq
    have hi := columnRepresentative_label label perfect i
    have hj := columnRepresentative_label label perfect j
    by_cases hri : ri ∈ perfect <;> by_cases hrj : rj ∈ perfect
    · rw [ite_eq_left hri, ite_eq_left hrj] at heq
      exact hi.symm.trans (((hname ri hri rj hrj).mp
        (perfectColumnName_injective heq)).trans hj)
    · rw [ite_eq_left hri, ite_eq_right hrj] at heq
      exact (perfectColumnName_ne_fresh _ _ heq).elim
    · rw [ite_eq_right hri, ite_eq_left hrj] at heq
      exact (perfectColumnName_ne_fresh _ _ heq.symm).elim
    · rw [ite_eq_right hri, ite_eq_right hrj] at heq
      have hr : ri = rj := Fin.ext (CanonicalColumnLabel.freshImperfect.inj heq)
      exact hi.symm.trans ((congrArg label hr).trans hj)
  · exact canonicalColumnName_of_label_eq label perfect name

noncomputable def canonicalPerfectEntries (label : Fin N → α) (perfect : Finset (Fin N))
    (name : Fin N → ℕ ⊕ ℕ) : List (Option CanonicalColumnLabel) :=
  List.ofFn (fun i => if i ∈ perfect then some (canonicalColumnName label perfect name i) else none)

/-- Looking up the canonical representative yields the intended class name,
including when the class has no perfect occurrence. -/
theorem canonical_reference_resolves (label : Fin N → α) (perfect : Finset (Fin N))
    (name : Fin N → ℕ ⊕ ℕ) (i : Fin N) :
    resolveColumnReference (canonicalPerfectEntries label perfect name)
      (columnRepresentative label perfect i).val = canonicalColumnName label perfect name i := by
  let j := columnRepresentative label perfect i
  have hj : j.val < N := j.isLt
  have heq : canonicalColumnName label perfect name j = canonicalColumnName label perfect name i :=
    canonicalColumnName_of_label_eq label perfect name (columnRepresentative_label label perfect i)
  have hget : (canonicalPerfectEntries label perfect name)[j.val]? =
      some (if j ∈ perfect then some (canonicalColumnName label perfect name j) else none) := by
    simp only [canonicalPerfectEntries, List.getElem?_ofFn, dite_eq_left hj, Fin.eta]
  change ((canonicalPerfectEntries label perfect name)[j.val]?.join).getD
    (.freshImperfect j.val) = _
  rw [hget]
  by_cases hp : j ∈ perfect
  · rw [ite_eq_left hp]
    exact heq
  · rw [ite_eq_right hp]
    change .freshImperfect j.val = canonicalColumnName label perfect name i
    symm
    exact ite_eq_right hp

def columnPositionEntries (perfect : Finset (Fin N)) : List (Fin N × Bool) :=
  List.ofFn (fun i => (i, decide (i ∈ perfect)))

theorem marked_position_entries (label : Fin N → α) (perfect : Finset (Fin N))
    (name : Fin N → ℕ ⊕ ℕ) :
    markedColumn (canonicalColumnName label perfect name) (columnPositionEntries perfect) =
      canonicalPerfectEntries label perfect name := by
  simp [markedColumn, columnPositionEntries, canonicalPerfectEntries, List.map_ofFn,
    Function.comp_def]

/-- All imperfect attachments are now verified for the actual occurrence
representatives, rather than supplied as lookup assumptions. -/
theorem canonical_imperfect_reconstruction (label : Fin N → α) (perfect : Finset (Fin N))
    (name : Fin N → ℕ ⊕ ℕ) :
    attachImperfectLabels (canonicalPerfectEntries label perfect name)
        (canonicalPerfectEntries label perfect name)
        (imperfectColumnReferences (fun i => (columnRepresentative label perfect i).val)
          (columnPositionEntries perfect)) =
      List.ofFn (canonicalColumnName label perfect name) := by
  have h := attachImperfectLabels_recover (canonicalPerfectEntries label perfect name)
    (canonicalColumnName label perfect name)
    (fun i => (columnRepresentative label perfect i).val) (columnPositionEntries perfect)
    (fun a _ _ => canonical_reference_resolves label perfect name a.1)
  rw [marked_position_entries] at h
  simpa only [columnPositionEntries, List.map_ofFn, Function.comp_def] using h

end TwoPointCorrelations

end OAI
