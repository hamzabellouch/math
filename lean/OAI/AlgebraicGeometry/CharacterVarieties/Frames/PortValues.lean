import OAI.AlgebraicGeometry.CharacterVarieties.Frames.FramedFlags

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport

/-- Frame values depend only on the ports and ranks, hence are unchanged by the
choice of boundary enumeration. -/
lemma frameValues_canonical {F S V K : Type} {arity : S → ℕ}
    [CommRing K] [Finite S] (D : Diagram F S V arity)
    (frames : D.PortFrames (R:=K)) (s : S) (b : Bool) :
    D.frameValues frames s b =
      (SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).frameValues frames s b := rfl

/-- A frame generator evaluates in the canonical boundary presentation using the
same port frame. -/
lemma valuesFromPorts_frame_canonical {F S V K : Type} {arity : S → ℕ}
    [CommRing K] [Finite S] (D : Diagram F S V arity)
    (frames : D.PortFrames (R:=K)) (side : D.SideValues (R:=K))
    (handle : D.HandleValues (R:=K)) (s : S) (b : Bool) :
    D.valuesFromPorts frames side handle (.frame s b) =
      (SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).frameValues frames s b := rfl

/-- Evaluating and reindexing a frame does not depend on the boundary enumeration. -/
lemma valuesFromPorts_frameCoordinates_canonical {F S V K α β : Type} {arity : S → ℕ}
    [CommRing K] [Finite S] [Fintype α] [Fintype β] (D : Diagram F S V arity)
    (frames : D.PortFrames (R:=K)) (side : D.SideValues (R:=K))
    (handle : D.HandleValues (R:=K)) (s : S) (b : Bool)
    (e : α ≃ Fin (D.seamDim s)) (f : β ≃ Fin (D.seamDim s)) :
    ((MatrixIso.unit (D.valuesFromPorts frames side handle (.frame s b))).reindex e f).linearEquiv =
      ((MatrixIso.unit ((SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).frameValues
        frames s b)).reindex e f).linearEquiv := rfl

/-- The evaluated parent coordinates use only the port and rank data. -/
lemma valuesFromPorts_parentCoordinates_canonical {F S V K R α : Type} {arity : S → ℕ}
    [CommRing K] [CommRing R] [Finite S] [Fintype α] (D : Diagram F S V arity)
    (frames : D.PortFrames (R:=K)) (side : D.SideValues (R:=K))
    (handle : D.HandleValues (R:=K)) (s : S) (φ : R →+* K)
    (e : α ≃ Fin (D.seamDim s)) :
    ((MatrixIso.unit ((D.parentWord s).eval φ (D.valuesFromPorts frames side handle))).reindex e e).linearEquiv =
      ((MatrixIso.unit (((SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).parentWord s).eval φ
        ((SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).valuesFromPorts
          frames side handle))).reindex e e).linearEquiv := by
  unfold parentWord
  erw [Term.eval_cast_unit φ (D.valuesFromPorts frames side handle) (D.seamRank s),
    Term.eval_cast_unit φ
      ((SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).valuesFromPorts frames side handle)
      (D.seamRank s)]
  rfl

/-- The evaluated inverse child coordinates use only the port and rank data. -/
lemma valuesFromPorts_childCoordinates_canonical {F S V K R α : Type} {arity : S → ℕ}
    [CommRing K] [CommRing R] [Finite S] [Fintype α] (D : Diagram F S V arity)
    (frames : D.PortFrames (R:=K)) (side : D.SideValues (R:=K))
    (handle : D.HandleValues (R:=K)) (s : S) (φ : R →+* K)
    (e : α ≃ Fin (D.seamDim s)) :
    ((MatrixIso.unit ((Term.block (D.childDim s) (fun j => Term.inv (D.childWord s j))).eval φ
      (D.valuesFromPorts frames side handle))).reindex e e).linearEquiv =
      ((MatrixIso.unit ((Term.block
        ((SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).childDim s)
        (fun j => Term.inv ((SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).childWord s j))).eval φ
        ((SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).valuesFromPorts
          frames side handle))).reindex e e).linearEquiv := rfl

/-- Child coordinates for values induced by ports and side transports. -/
lemma valuesFromPorts_childWord_coordinates
    {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K]
    (D : Diagram F S V arity) (s : S) (φ : R →+* K)
    (frames : D.PortFrames (R:=K)) (side : D.SideValues (R:=K))
    (handle : D.HandleValues (R:=K)) {m : ℕ} (d : Fin m → ℕ)
    (c : Fin m ≃ Fin (arity s)) (hc : ∀ i,d i=D.childDim s (c i))
    (old : (i : Fin m) → (Matrix (Fin (d i)) (Fin (d i)) K)ˣ)
    (ho : ∀ i,rebaseUnit (hc i).symm (side ⟨s,some (c i)⟩)=old i)
    (e : ((i : Fin m) × Fin (d i)) ≃ Fin (D.seamDim s))
    (he : e=(Equiv.sigmaCongr c (fun i=>finCongr (hc i))).trans
      (blockIndex (D.childDim s)).symm) :
    ((MatrixIso.unit ((Term.block (D.childDim s)
      (fun j => Term.inv (D.childWord s j))).eval φ
        (D.valuesFromPorts frames side handle))).reindex e e).linearEquiv=
      (MatrixIso.block (fun i=>MatrixIso.unit (old i)⁻¹)).linearEquiv := by
  exact D.childWord_coordinates s φ (D.valuesFromPorts frames side handle)
    d c hc old ho e he

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
