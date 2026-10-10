import OAI.AlgebraicGeometry.CharacterVarieties.Seams.InternalSeams

namespace OAI

/-!
# Seam equations from port values

Identity side transports and equal port frames imply the framed seam equation.
-/

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression HomTransport

/-- Port values with trivial side transports and equal frames satisfy the seam equation. -/
lemma valuesFromPorts_trivialSides_seamHolds
    {F S V R K : Type} {arity : S → ℕ} [CommRing R] [CommRing K]
    (D : Diagram F S V arity) (φ : R →+* K)
    (frames : D.PortFrames (R:=K)) (side : D.SideValues (R:=K))
    (handle : D.HandleValues (R:=K)) (s : S)
    (hs : ∀ i : Option (Fin (arity s)), side ⟨s,i⟩=1)
    (hf : D.frameValues frames s false=D.frameValues frames s true) :
    SameFramedFlag (D.seamGrade s)
      (matrixUnitEquiv ((D.seamLeft s).eval φ (D.valuesFromPorts frames side handle)))
      (matrixUnitEquiv ((D.seamRight s).eval φ (D.valuesFromPorts frames side handle))) := by
  exact D.trivialSides_seamHolds φ (D.valuesFromPorts frames side handle) s
    (hs none) (fun i => hs (some i)) hf

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
