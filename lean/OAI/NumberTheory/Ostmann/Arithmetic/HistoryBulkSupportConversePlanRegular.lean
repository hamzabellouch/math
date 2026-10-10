import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFieldIndependence
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportRowsCoefficients

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConversePlan
open Construction CanonicalOccurrenceTransport HistoryOccurrenceVariables HistorySymbolicEncoding
open Characters.RationalHistory
variable {K : Type*} [Field K]

theorem coordinate_ancestor_units (seed : List SourceSlot) {l : ℕ}
    (h : History l) (hh : TreeSourceLabels seed h) (i : Internal seed l)
    (x : Coordinate seed l → K)
    (hx : ∀q : Fin (Template.current seed l).length ⊕ Internal seed l,
      CanonicalOccurrenceTransport.internalLevel seed i < coordinateLevel seed l (.inr q) →
        x (.inr q) ≠ 0) :
    ∀q : Fin h.root.small.length ⊕ InternalKey h,
      HistoryOccurrenceVariables.internalLevel h (internalEquiv seed h hh i) <
          keyLevel h (.inr q) →
        (x ∘ (coordinateEquiv seed h hh).symm) (.inr q) ≠ 0 := by
  intro q hq
  obtain ⟨r,hr⟩ := (coordinateEquiv seed h hh).surjective (.inr q)
  cases r with
  | inl b =>
    change Sum.inl b = Sum.inr q at hr
    cases hr
  | inr r =>
    have hl := coordinateEquiv_level seed h hh (.inr r)
    rw [hr] at hl
    have hi := internalEquiv_level seed h hh i
    have hlt : CanonicalOccurrenceTransport.internalLevel seed i <
        coordinateLevel seed l (.inr r) := by
      rw [←hl,←hi]
      exact hq
    change x ((coordinateEquiv seed h hh).symm (.inr q)) ≠ 0
    rw [←hr,Equiv.symm_apply_apply]
    exact hx r hlt

theorem normalizedRows_regular (seed : List SourceSlot) {l : ℕ}
    {V : ℕ → ℕ} {outside : List ℕ} (h : History l) (hs : h.Supported V outside)
    (hh : TreeSourceLabels seed h) (i : Internal seed l) (x : Coordinate seed l → K)
    (hx : ∀q : Fin (Template.current seed l).length ⊕ Internal seed l,
      CanonicalOccurrenceTransport.internalLevel seed i < coordinateLevel seed l (.inr q) →
        x (.inr q) ≠ 0)
    (hf : ∀s ∈ h.frequencies,(s:K) ≠ 0) :
    (normalizedRows seed h hs hh i).1.FieldRegularAt x ∧
      (normalizedRows seed h hs hh i).2.FieldRegularAt x := by
  have hr := HistoryFieldIndependence.canonical_regular h hs (internalEquiv seed h hh i)
    (x ∘ (coordinateEquiv seed h hh).symm) (coordinate_ancestor_units seed h hh i x hx) hf
  simpa only [normalizedRows,Expr.fieldRegularAt_rename] using hr

end Ostmann.Arithmetic.HistoryBulkSupportConversePlan

end

end OAI
