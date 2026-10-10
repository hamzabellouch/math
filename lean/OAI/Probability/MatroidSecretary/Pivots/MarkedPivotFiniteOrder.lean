import OAI.Probability.MatroidSecretary.Pivots.MarkedPivotSpecification
import OAI.Probability.MatroidSecretary.Pivots.PivotOrderInvariance

namespace OAI

/-!
# Exact finite interleavings for the source-level marked-pivot family

This bridge applies directly to the finite-old specification, including an
empty label type. It does not extend an old list to an infinite sequence.
-/

namespace MatroidProphet.MarkedPivots

variable {α : Type*} {r q n : ℕ}

lemma firstSpans_orderPosition_iff (M : Matroid α)
    (labels : Occurrences r q → α) (time : Occurrences r q → ℕ)
    (e : α) (o : Occurrences r q) :
    FirstSpans M labels (Pivots.orderPosition time) e o ↔
      FirstSpans M labels time e o :=
  Pivots.isPivot_orderPosition_iff M labels time e o

lemma records_orderPosition_iff (M : Matroid α)
    (old : Fin r → α) (movable : Fin q → α) (test : Fin n → α)
    (time : Occurrences r q → ℕ) (oldMark : Fin r → Bool)
    (movableMark : Fin q → Bool) (pattern : Finset (Fin n)) :
    Records M old movable test (Pivots.orderPosition time) oldMark movableMark pattern ↔
      Records M old movable test time oldMark movableMark pattern := by
  simp only [Records, firstSpans_orderPosition_iff]

lemma oldOrdered_orderPosition_iff (time : Occurrences r q → ℕ) :
    OldOrdered (Pivots.orderPosition time) ↔ OldOrdered time := by
  simp only [OldOrdered, Pivots.orderPosition_lt_iff]

/-- The source family is exactly the family obtained by permuting the finite
occurrence set into its finite set of positions, keeping the old order.
No inhabitedness or distinctness assumption on labels is needed. -/
theorem mem_patterns_iff_finite_order (M : Matroid α)
    (old : Fin r → α) (movable : Fin q → α) (test : Fin n → α)
    (oldMark : Fin r → Bool) (pattern : Finset (Fin n)) :
    pattern ∈ patterns M old movable test oldMark ↔
      ∃ position : Occurrences r q ≃ Fin (Fintype.card (Occurrences r q)),
        OldOrdered (fun o => (position o).val) ∧
          ∃ movableMark : Fin q → Bool,
            Records M old movable test (fun o => (position o).val)
              oldMark movableMark pattern := by
  classical
  constructor
  · intro ht
    obtain ⟨time, horder, htime, movableMark, hrecords⟩ := (Finset.mem_filter.mp ht).2
    let position := Equiv.ofBijective (Pivots.finiteOrderPosition time)
      (Pivots.finiteOrderPosition_bijective time htime)
    refine ⟨position, ?_, movableMark, ?_⟩
    · change OldOrdered (Pivots.orderPosition time)
      exact (oldOrdered_orderPosition_iff time).mpr horder
    · change Records M old movable test (Pivots.orderPosition time)
        oldMark movableMark pattern
      exact (records_orderPosition_iff M old movable test time
        oldMark movableMark pattern).mpr hrecords
  · rintro ⟨position, horder, movableMark, hrecords⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (fun o => (position o).val),
      horder, (fun o p h => position.injective (Fin.ext h)), movableMark, hrecords⟩

end MatroidProphet.MarkedPivots

end OAI
