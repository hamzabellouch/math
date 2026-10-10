import OAI.Analysis.KadisonKastler.ProjectionStratumOperators
import OAI.Analysis.KadisonSimilarity.Representation.NonunitalRangeRepresentation

namespace OAI

/-! # Fixed-coordinate representations on measurable rank strata -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped lp

noncomputable section

variable {X A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (ρ : X → A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

abbrev representationUnitProjection : X → H →L[ℂ] H := fun x => nonunitalUnitProjection (ρ x)

theorem representationUnitProjection_idempotent (x : X) :
    IsIdempotentElem (representationUnitProjection ρ x) :=
  (nonunitalUnitProjection_isStarProjection (ρ x)).isIdempotentElem

/-- A nonunital ambient field acts unitally on each fixed-coordinate range. -/
def fixedFiberRepresentation (n : ℕ)
    (x : projectionRankStratum (representationUnitProjection ρ) b n) :
    A →⋆ₐ[ℂ] (ℓ²(projectionDimensionIndex n, ℂ) →L[ℂ] ℓ²(projectionDimensionIndex n, ℂ)) := by
  letI : CompleteSpace (representationUnitProjection ρ x.val).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      (representationUnitProjection_idempotent ρ x.val)).completeSpace_coe
  exact (projectionStratumCoordinates (representationUnitProjection ρ)
    (representationUnitProjection_idempotent ρ) b hb n x).conjStarAlgEquiv.toStarAlgHom.comp
      (nonunitalRangeRepresentation (ρ x.val))

theorem representationUnitProjection_invariant (a : A) (x : X) :
    ∀ v ∈ (representationUnitProjection ρ x).range,
      ρ x a v ∈ (representationUnitProjection ρ x).range :=
  projectionFiber_invariant _ (nonunitalUnitProjection_isStarProjection (ρ x))
    _ (nonunitalUnitProjection_commutes (ρ x) a)

theorem fixedFiberRepresentation_eq (n : ℕ)
    (x : projectionRankStratum (representationUnitProjection ρ) b n) (a : A) :
    fixedFiberRepresentation ρ b hb n x a =
      projectionStratumOperator (representationUnitProjection ρ)
        (representationUnitProjection_idempotent ρ) b hb (fun x => ρ x a)
        (representationUnitProjection_invariant ρ a) n x := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

variable [MeasurableSpace X] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]

theorem fixedFiberRepresentation_measurable
    (hρ : ∀ a v, Measurable fun x => ρ x a v) (n : ℕ)
    [MeasurableSpace ℓ²(projectionDimensionIndex n, ℂ)]
    [BorelSpace ℓ²(projectionDimensionIndex n, ℂ)]
    (a : A) (v : ℓ²(projectionDimensionIndex n, ℂ)) :
    Measurable fun x => fixedFiberRepresentation ρ b hb n x a v := by
  simp_rw [fixedFiberRepresentation_eq]
  exact projectionStratumOperator_measurable _ _ b hb (hρ 1) _ (hρ a) _ n v

end

end KadisonKastler

end OAI
