import OAI.NumberTheory.TwoPoint.Bounds.RegularQuotient

namespace OAI

/-! Choosing one common affine line for all lit occurrences of each regular label. -/

namespace TwoPointCorrelations

open Finset Submodule

variable {K α ι : Type*} [Field K] [Fintype α] [Fintype ι]
  [DecidableEq α] [DecidableEq ι]

/-- A low-rank family gives independent regular directions and one anchor
per label, shared by every lit departure in every perfect block. -/
theorem exists_regular_line_anchors (label : ι → α) (offset : ι → α → K) (r : ℕ)
    (hno : ∀ S : Finset (EqualLabelPairs label), S.card = r →
      ¬LinearIndependent K (pairFamily (labelPairVectors label offset) S)) :
    ∃ (D : Submodule K (α → K)) (R : Finset α)
      (anchor : R → (α → K) ⧸ D), Rᶜ.card < 2 * r ∧
      LinearIndependent K (fun z : R => D.mkQ (Pi.basisFun K α z)) ∧
      ∀ (z : R) i, label i = z →
        ∃ c : K, D.mkQ (offset i) = anchor z + c • D.mkQ (Pi.basisFun K α z) := by
  classical
  obtain ⟨D, R, hcard, hind, _, hline⟩ := exists_regular_quotient label offset r hno
  let anchor : R → (α → K) ⧸ D := fun z =>
    if h : ∃ i, label i = z then D.mkQ (offset h.choose) else 0
  refine ⟨D, R, anchor, hcard, hind, ?_⟩
  intro z i hi
  have hex : ∃ j, label j = z := ⟨i, hi⟩
  obtain ⟨c, hc⟩ := hline z i hex.choose hi hex.choose_spec
  refine ⟨c, ?_⟩
  simpa only [anchor, dite_eq_left hex] using hc

end TwoPointCorrelations

end OAI
