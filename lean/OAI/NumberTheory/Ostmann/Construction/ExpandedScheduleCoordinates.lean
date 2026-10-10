import OAI.NumberTheory.Ostmann.Construction.ExpandedScheduleState

namespace OAI

/-! # Fresh finite pivot coordinates for expanded prime-word templates -/

namespace Ostmann

open scoped Classical

abbrev ExpandedScheduledVariable (α : Type*) (depth : ℕ) :=
  α ⊕ (Fin (depth + 1) × (Fin depth → Bool))

def expandedPivotAddress (α : Type*) (depth j : ℕ) (path : List Bool) : ExpandedScheduledVariable α depth :=
  .inr (⟨j % (depth + 1), Nat.mod_lt _ (by omega)⟩, fun i => path.getD i.val false)

def ExpandedCoordinateAfter {α : Type*} {depth : ℕ} (j : ℕ) : ExpandedScheduledVariable α depth → Prop
  | .inl _ => True
  | .inr p => j ≤ p.1.val

theorem ExpandedCoordinateAfter.mono {α : Type*} {depth j k : ℕ}
    {v : ExpandedScheduledVariable α depth} (h : ExpandedCoordinateAfter k v) (hjk : j ≤ k) :
    ExpandedCoordinateAfter j v := by
  cases v with
  | inl a => trivial
  | inr p => exact hjk.trans h

theorem expandedPivotAddress_after (α : Type*) (depth j : ℕ) (hj : j ≤ depth) (path : List Bool) :
    ExpandedCoordinateAfter j (expandedPivotAddress α depth j path) := by
  change j ≤ j % (depth + 1)
  rw [Nat.mod_eq_of_lt (by omega)]

theorem expandedPivotAddress_fresh {α : Type*} {depth j : ℕ} (hj : j ≤ depth)
    (path : List Bool) (v : ExpandedScheduledVariable α depth)
    (hv : ExpandedCoordinateAfter (j + 1) v) : v ≠ expandedPivotAddress α depth j path := by
  intro he
  subst v
  change j + 1 ≤ j % (depth + 1) at hv
  rw [Nat.mod_eq_of_lt (by omega)] at hv
  omega

/-- Descending one level adds just its reconstructed pivot coordinate;
all inherited coordinates still lie strictly above the next pivot level. -/
theorem reverseExpandedCoordinates_after {I α : Type*} (role : I → CopyScheduleRole)
    (depth j : ℕ) (hj : j ≤ depth) (b : Bool) (path : List Bool)
    (current : CopyScheduleAtoms role (j + 1) → List (ExpandedScheduledVariable α depth))
    (hc : ∀ i v, v ∈ current i → ExpandedCoordinateAfter (j + 1) v) :
    ∀ i v, v ∈ reverseCopyLabelMap role j b [expandedPivotAddress α depth j path] current i →
      ExpandedCoordinateAfter j v := by
  intro i v hv
  unfold reverseCopyLabelMap at hv
  split_ifs at hv
  · exact (hc _ v hv).mono (by omega)
  · have he : v = expandedPivotAddress α depth j path := List.mem_singleton.mp hv
    rw [he]
    exact expandedPivotAddress_after α depth j hj path
  · exact (hc _ v hv).mono (by omega)

noncomputable def expandedRootTemplate {I α : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth : ℕ) (words : CopyScheduleAtoms role depth → List α)
    (childBound pivotBound : ℕ → ℕ) : WordTransferTemplate (ExpandedScheduledVariable α depth) depth :=
  expandedScheduledTemplate role (expandedPivotAddress α depth) childBound pivotBound depth []
    (fun i => (words i).map Sum.inl)

theorem expandedRootCoordinates_after {I α : Type*} (role : I → CopyScheduleRole)
    (depth : ℕ) (words : CopyScheduleAtoms role depth → List α) :
    ∀ i v, v ∈ (words i).map (Sum.inl : α → ExpandedScheduledVariable α depth) →
      ExpandedCoordinateAfter depth v := by
  intro i v hv
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
  trivial

/-- The prime-expanded template has a concrete polynomial word bound. -/
theorem expandedRootTemplate_size {I α : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth : ℕ) (words : CopyScheduleAtoms role depth → List α)
    (childBound pivotBound : ℕ → ℕ) (M : ℕ) (hM : 1 ≤ M)
    (hwords : ∀ i, (words i).length ≤ M) :
    (expandedRootTemplate role depth words childBound pivotBound).WordsBounded
      (2 * 3 ^ depth * Fintype.card I * M + 4) := by
  apply expandedScheduledTemplate_words_bounded role _ _ _ depth M _ hM
  · rw [copyScheduleAtoms_zero_card]
    have hp : 1 ≤ 3 ^ depth := Nat.one_le_pow _ _ (by omega)
    have hm := Nat.mul_le_mul_right (Fintype.card I * M) hp
    nlinarith only [hm]
  · intro j hj
    have hc := copyScheduleH_card_le role j
    have hp : 3 ^ j ≤ 3 ^ depth := Nat.pow_le_pow_right (by omega) (by omega)
    have hmul := Nat.mul_le_mul_right (Fintype.card I) hp
    have hmulM := Nat.mul_le_mul_right M (hc.trans hmul)
    nlinarith
  · intro i
    simpa only [List.length_map] using hwords i

end Ostmann

end OAI
