import OAI.AlgebraicGeometry.CharacterVarieties.Frames.PortValues

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression HomTransport

/-- The evaluated framed flag equation depends only on the ports and ranks, not on the
boundary enumeration. -/
lemma valuesFromPorts_seamHolds_canonical
    {F S V K R : Type} {arity : S → ℕ} [Field K] [CommRing R] [Finite S]
    (D : Diagram F S V arity) (frames : D.PortFrames (R:=K))
    (side : D.SideValues (R:=K)) (handle : D.HandleValues (R:=K))
    (s : S) (φ : R →+* K) :
    SameFramedFlag (D.seamGrade s)
      (matrixUnitEquiv ((D.seamLeft s).eval φ (D.valuesFromPorts frames side handle)))
      (matrixUnitEquiv ((D.seamRight s).eval φ (D.valuesFromPorts frames side handle))) ↔
    SameFramedFlag ((SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).seamGrade s)
      (matrixUnitEquiv
        (((SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).seamLeft s).eval φ
          ((SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).valuesFromPorts
            frames side handle)))
      (matrixUnitEquiv
        (((SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).seamRight s).eval φ
          ((SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).valuesFromPorts
            frames side handle))) := by
  have hl : (D.seamLeft s).eval φ (D.valuesFromPorts frames side handle) =
      ((SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).seamLeft s).eval φ
        ((SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).valuesFromPorts
          frames side handle) := by
    simp only [seamLeft, Term.eval]
    unfold parentWord
    erw [Term.eval_cast_unit φ (D.valuesFromPorts frames side handle) (D.seamRank s),
      Term.eval_cast_unit φ
        ((SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).valuesFromPorts
          frames side handle) (D.seamRank s)]
    rfl
  have hr : (D.seamRight s).eval φ (D.valuesFromPorts frames side handle) =
      ((SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).seamRight s).eval φ
        ((SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).valuesFromPorts
          frames side handle) := rfl
  rw [hl, hr]
  rfl

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
