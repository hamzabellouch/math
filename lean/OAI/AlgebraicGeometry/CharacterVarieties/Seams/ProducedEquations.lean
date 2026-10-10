import OAI.AlgebraicGeometry.CharacterVarieties.Seams.ProducedDiagram

namespace OAI

/-!
# Framed seam equations on the produced marked diagram

The complete seam equations and the first short-seam equation use the
marked diagram and generator values determined by a field-valued solution.
-/

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hproper : D.Proper) (hmax : ∀ f, D.rank f ≤ D.rank (D.ports.facet ⟨q,none⟩))
    (hg : 0 < D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))

/-- The framed flag equations at every produced marked seam. -/
def ProducedMarkedSeamEquations : Prop :=
    let C := D.producedMarkedDiagram q hproper hmax hg P x b0 i0
    let v := D.producedMarkedValues q hproper hmax hg P x b0 i0
    ∀ s, SameFramedFlag (C.seamGrade s)
      (matrixUnitEquiv ((C.seamLeft s).eval (algebraMap R K) v))
      (matrixUnitEquiv ((C.seamRight s).eval (algebraMap R K) v))

/-- The framed flag equation at the first produced short seam. -/
def ProducedMarkedFirstShortEquation : Prop :=
    let w := D.producedCutBand q hg P x b0 i0
    let A := D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
    let B := D.ports.refinedBandForSeam q w.shape
    let s := BandGraft.originalPort A q B 0 true
    SameFramedFlag
      ((D.producedMarkedDiagram q hproper hmax hg P x b0 i0).seamGrade s)
      (matrixUnitEquiv
        (((D.producedMarkedDiagram q hproper hmax hg P x b0 i0).seamLeft s).eval
          (algebraMap R K) (D.producedMarkedValues q hproper hmax hg P x b0 i0)))
      (matrixUnitEquiv
        (((D.producedMarkedDiagram q hproper hmax hg P x b0 i0).seamRight s).eval
          (algebraMap R K) (D.producedMarkedValues q hproper hmax hg P x b0 i0)))

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
