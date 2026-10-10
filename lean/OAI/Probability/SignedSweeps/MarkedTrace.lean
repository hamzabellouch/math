import OAI.Probability.SignedSweeps.ProjectionTrace
import OAI.Probability.SignedSweeps.MarkedMultiplicity
import OAI.Probability.SignedSweeps.CoefficientAlgebra

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma markedSector_trace {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (f : SymmetricGroup n → ℂ) :
    LinearMap.trace ℂ (MarkedWordSpace p l n C)
      (markedTypeProjection hu h a b C * coefficientAction (markedWordRepresentation h C) f) =
        LinearMap.trace ℂ (MarkedSectorSpace hu h a b C)
          (coefficientAction (markedSectorRepresentation hu h a b C) f) :=
  projectionSubrepresentation_trace (markedWordRepresentation h C)
    (markedTypeProjection hu h a b C) (markedTypeProjection_idempotent hu h a b C)
    (markedTypeProjection_commute hu h a b C) f

lemma markedSector_product_trace {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (a : Partition u) (b : Partition v)
    (f k : SymmetricGroup n → ℂ) :
    LinearMap.trace ℂ (MarkedWordSpace p l n C)
      (markedTypeProjection hu h a b C * coefficientAction (markedWordRepresentation h C) f *
        coefficientAction (markedWordRepresentation h C) k) =
        LinearMap.trace ℂ (MarkedSectorSpace hu h a b C)
          (coefficientAction (markedSectorRepresentation hu h a b C) f *
            coefficientAction (markedSectorRepresentation hu h a b C) k) := by
  rw [mul_assoc, ← coefficientAction_mul, ← coefficientAction_mul]
  exact markedSector_trace hu h a b _

theorem signed_occurrence_marked_trace {u v p l n : ℕ} {C : Type*} [Fintype C]
    (hu : u+v=p) (h : p+l=n) (hn : u+v+l=n)
    (a : Partition u) (b : Partition v) (c : Partition l) (lam : Partition n)
    (colorA : Fin (a.1.colLen 0) ↪ C) (colorB : Fin (b.1.colLen 0) ↪ C)
    (hocc : SignedOccurrence hn a b c lam) (z : MarkedAssignment l n) (S : EvenAllocation u p)
    (f k : SymmetricGroup n → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive)
    (hk : (coefficientAction finiteRegularRepresentation k).IsPositive) :
    (spechtDimension c : ℝ) * (LinearMap.trace ℂ (Specht lam)
      (coefficientAction (spechtRepresentation lam) f * coefficientAction (spechtRepresentation lam) k)).re ≤
        (LinearMap.trace ℂ (MarkedWordSpace p l n C)
          (markedTypeProjection hu h a b C * coefficientAction (markedWordRepresentation h C) f *
            coefficientAction (markedWordRepresentation h C) k)).re := by
  rw [markedSector_product_trace hu h a b f k]
  exact multiplicity_positive_product_trace (markedSectorRepresentation hu h a b C) f k hf hk lam _
    (signed_occurrence_marked_multiplicity hu h hn a b c lam colorA colorB hocc z S)

end SignedSweeps
end

end OAI
