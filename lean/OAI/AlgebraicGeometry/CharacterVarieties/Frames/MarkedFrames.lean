import OAI.AlgebraicGeometry.CharacterVarieties.Frames.Mirror
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.NamedSeams
import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.MarkedDiagram

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression NamedBandGrades
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (J : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
/-- A simultaneous splitting for arbitrary original generator coordinates, including the circle-
gauged coordinates of the surface equation. -/
opaque cutGeneratorWitness : IdentifiedBand (D.childDim q)
    (D.namedSeamFrame q (g (.frame q false)))
    (((D.namedSeamFrame q (g (.frame q false))).trans (D.namedParentLinear q g)).trans
      (MatrixIso.unit J).linearEquiv.symm) :=
  identifiedBand (D.namedSeamFrame q (g (.frame q false)))
    (((D.namedSeamFrame q (g (.frame q false))).trans (D.namedParentLinear q g)).trans
      (MatrixIso.unit J).linearEquiv.symm)
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression NamedBandGrades
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))

def markedCutFrames : (D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax).PortFrames (R:=K) :=
  D.namedCutPortFrames q w old T

lemma markedCutFrames_holds
    (hold : ∀ v,(VertexTable.LocalRanks.comparison (D.ports.kind v) (D.vertexRanks v)
      (fun p => old ⟨v,p⟩)).Holds) :
    ∀ v,(VertexTable.LocalRanks.comparison
      ((D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax).ports.kind v)
      ((D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax).vertexRanks v)
      (fun p => D.markedCutFrames q w hproper hmax old T ⟨v,p⟩)).Holds :=
  D.namedCutPortFrames_holds q w old T hold

lemma marked_values_vertexHolds
    (oldHolds : ∀ v,(VertexTable.LocalRanks.comparison (D.ports.kind v) (D.vertexRanks v)
      (fun p => old ⟨v,p⟩)).Holds)
    (s : (D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax).SideValues (R:=K))
    (hh : (D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax).HandleValues (R:=K)) :
    (D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax).VertexHolds
      ((D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax).valuesFromPorts
        (D.markedCutFrames q w hproper hmax old T) s hh) := by
  exact @vertexHolds_valuesFromPorts _ _ _ K _ _
    (D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax)
    (D.markedCutFrames q w hproper hmax old T) s hh
    (D.markedCutFrames_holds q w hproper hmax old T oldHolds)
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
