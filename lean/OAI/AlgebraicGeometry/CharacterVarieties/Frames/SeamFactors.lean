import OAI.AlgebraicGeometry.CharacterVarieties.Frames.FramedFlags

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open MatrixExpression HomTransport
variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K]
    (D : Diagram F S V arity) (s : S) (φ : R →+* K)
    (g : (e : D.Generator) →
      (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    {α β : Type} [Fintype α] [Fintype β]

/-- Coordinates of the left seam word compose the frame and parent transports. -/
lemma seamLeft_coordinates
    (e : α ≃ Fin (D.seamDim s)) (f : β ≃ Fin (D.seamDim s))
    (x : (α → K) ≃ₗ[K] (β → K)) (p : (β → K) ≃ₗ[K] (β → K))
    (hx : ((MatrixIso.unit (g (.frame s false))).reindex e f).linearEquiv=x)
    (hp : ((MatrixIso.unit ((D.parentWord s).eval φ g)).reindex f f).linearEquiv=p) :
    ((MatrixIso.unit ((D.seamLeft s).eval φ g)).reindex e f).linearEquiv=x.trans p := by
  simp only [seamLeft, Term.eval, frameWord]
  erw [MatrixIso.unit_mul, MatrixIso.reindex_trans _ _ e f f,
    MatrixIso.linearEquiv_trans_eq, hx, hp]

/-- Coordinates of the right seam word compose the child inverse and frame transports. -/
lemma seamRight_coordinates
    (e : α ≃ Fin (D.seamDim s)) (f : β ≃ Fin (D.seamDim s))
    (y : (α → K) ≃ₗ[K] (β → K)) (u : (α → K) ≃ₗ[K] (α → K))
    (hy : ((MatrixIso.unit (g (.frame s true))).reindex e f).linearEquiv=y)
    (hu : ((MatrixIso.unit ((Term.block (D.childDim s)
      (fun j => Term.inv (D.childWord s j))).eval φ g)).reindex e e).linearEquiv=u) :
    ((MatrixIso.unit ((D.seamRight s).eval φ g)).reindex e f).linearEquiv=u.trans y := by
  simp only [seamRight, Term.eval, frameWord]
  erw [MatrixIso.unit_mul, MatrixIso.reindex_trans _ _ e e f,
    MatrixIso.linearEquiv_trans_eq, hy]
  exact congrArg (fun z => z.trans y) hu

/-- Common coordinates for the two complete seam words determine their framed flag equation. -/
lemma seamHolds_of_wordCoordinates
    (e : α ≃ Fin (D.seamDim s)) (f : β ≃ Fin (D.seamDim s))
    (a : α → ℕ) (x y : (α → K) ≃ₗ[K] (β → K))
    (ha : ∀ i,D.seamGrade s (e i)=a i)
    (hx : ((MatrixIso.unit ((D.seamLeft s).eval φ g)).reindex e f).linearEquiv=x)
    (hy : ((MatrixIso.unit ((D.seamRight s).eval φ g)).reindex e f).linearEquiv=y)
    (hh : SameFramedFlag a x y) :
    SameFramedFlag (D.seamGrade s)
      (matrixUnitEquiv ((D.seamLeft s).eval φ g))
      (matrixUnitEquiv ((D.seamRight s).eval φ g)) := by
  exact MatrixIso.sameFramedFlag_of_coordinates (D.seamGrade s)
    (MatrixIso.unit ((D.seamLeft s).eval φ g))
    (MatrixIso.unit ((D.seamRight s).eval φ g)) e f a x y ha hx hy hh

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
