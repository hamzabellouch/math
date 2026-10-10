import OAI.NumberTheory.Ostmann.Construction.ScheduleGraphInvariants
import OAI.NumberTheory.Ostmann.Construction.ScheduleWordSlots
import OAI.NumberTheory.Ostmann.Construction.TransferCompletePhase

namespace OAI

/-! # Restricting the graph update to the actual H/Y partition -/

namespace Ostmann

/-- The input graph retains only the total pivot and the actual H/Y slots. -/
noncomputable def scheduledRetainedGraph {I : Type*} (role : I → CopyScheduleRole)
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ) :
    Option (CopyScheduleH role n ⊕ CopyScheduleY role n) →
      Option (CopyScheduleH role n ⊕ CopyScheduleY role n) → ℤ :=
  let old : Option (CopyScheduleH role n ⊕ CopyScheduleY role n) → CopyScheduleVertex I n := fun i =>
    match i with
    | none => copySchedulePositive n (pivot n)
    | some (.inl h) => h.val
    | some (.inr y) => y.val
  fun i j => copyScheduleGraph g pivot n (old i) (old j)

/-- No unused copied or retained alternative occurs in this map. -/
def scheduledOutputVertex {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :
    (Bool × CopyScheduleH role n) ⊕ CopyScheduleY role n →
      {i : CopyScheduleVertex I (n + 1) // CopyScheduleSurvives role (n + 1) i} :=
  (copyScheduleSurvivorEquiv role n).symm

/-- The graph used by the exact local phase formula is the restriction of
our recursively constructed graph to the genuine surviving slots. -/
theorem scheduledRetainedGraph_update {I : Type*} (role : I → CopyScheduleRole)
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ)
    (i j : (Bool × CopyScheduleH role n) ⊕ CopyScheduleY role n) :
    transferredGraph (scheduledRetainedGraph role g pivot n) i j =
      copyScheduleGraph g pivot (n + 1)
        (scheduledOutputVertex role n i).val (scheduledOutputVertex role n j).val := by
  cases i with
  | inl i =>
    rcases i with ⟨b, i⟩
    cases j with
    | inl j => rcases j with ⟨c, j⟩; rfl
    | inr j => rfl
  | inr i =>
    cases j with
    | inl j => rcases j with ⟨c, j⟩; rfl
    | inr j => rfl

theorem scheduledRetainedGraph_diagonal {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (i : Option (CopyScheduleH role n ⊕ CopyScheduleY role n)) :
    scheduledRetainedGraph role initialCompleteGraph pivot n i i = 0 :=
  copyScheduleGraph_diagonal initialCompleteGraph pivot initialCompleteGraph_self n _

/-- The pivot-column exponent in the local phase is independent of which
constituent is chosen to represent that active pivot group. -/
theorem scheduledRetainedGraph_pivot_column {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (hpivot : ∀ k, role (pivot k) = .pivot k)
    (n : ℕ) (p : I) (hp : role p = .pivot n)
    (i : CopyScheduleH role n ⊕ CopyScheduleY role n) :
    scheduledRetainedGraph role initialCompleteGraph pivot n (some i) none =
      copyScheduleGraph initialCompleteGraph pivot n
        (Sum.elim Subtype.val Subtype.val i) (copySchedulePositive n p) := by
  cases i with
  | inl i =>
    apply copyScheduleGraph_pivot_common_column role pivot n (pivot n) p (hpivot n) hp n le_rfl i.val i.property.1
    intro he
    have hc := i.property.2
    rw [he] at hc
    simp [CopyScheduleRole.copiedAt] at hc
  | inr i =>
    apply copyScheduleGraph_pivot_common_column role pivot n (pivot n) p (hpivot n) hp n le_rfl i.val i.property.1
    intro he
    have hc := i.property.2.2
    rw [he] at hc
    simp [CopyScheduleRole.erasedAt] at hc

/-- The regular row hypotheses required when removing the pivot factors
are consequences of the constructed graph and original role distinction. -/
theorem scheduledRetainedGraph_word_pivot {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (hpivot : ∀ k, role (pivot k) = .pivot k)
    (n : ℕ) (i : I) (hi : role i = .word) (t : Fin n → Bool)
    (h : CopyScheduleH role n) (hh : h.val = copySchedulePath n t i) :
    scheduledRetainedGraph role initialCompleteGraph pivot n (some (.inl h)) none =
      finalCopyParity t := by
  change copyScheduleGraph initialCompleteGraph pivot n h.val (copySchedulePositive n (pivot n)) = _
  rw [hh]
  apply scheduledRegularRow_word role pivot hpivot i hi n t
  · exact copyScheduleSurvives_positive role (pivot n) n (hpivot n) n le_rfl
  · intro he
    have hr := congrArg (copyScheduleRole role n) he
    rw [copyScheduleRole_positive role (pivot n) n (hpivot n), copyScheduleRole_path role i hi] at hr
    cases hr

end Ostmann

end OAI
