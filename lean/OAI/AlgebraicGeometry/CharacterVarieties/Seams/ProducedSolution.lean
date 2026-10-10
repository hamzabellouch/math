import OAI.AlgebraicGeometry.CharacterVarieties.Seams.AllSeams
import OAI.AlgebraicGeometry.CharacterVarieties.Seams.ProducedEquations

namespace OAI

/-!
# A solution on the produced marked diagram

Every seam of the produced marked diagram satisfies its framed flag
equation. The surface, seam, and vertex equations assemble a field-valued solution.
-/

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
/-- Equal generator values satisfy the same framed seam equations. -/
lemma framedSeamEquations_of_values_eq
    {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K]
    (C : Diagram F S V arity) (φ : R →+* K)
    {v v' : (e : C.Generator) →
      (Matrix (Fin (C.generatorRank e)) (Fin (C.generatorRank e)) K)ˣ}
    (h : v = v')
    (hseam : ∀ s, FramedSeamEquation (D:=C) (g:=v) (φ:=φ) s) :
    ∀ s, FramedSeamEquation (D:=C) (g:=v') (φ:=φ) s := by
  cases h
  exact hseam

variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K] [Algebra R K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (hproper : D.Proper) (hmax : ∀ f, D.rank f ≤ D.rank (D.ports.facet ⟨q,none⟩))
    (hg : 0 < D.genus (D.bandCutParent q))
    (P : D.Punctures R) (x : D.Solution P K)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))

theorem producedMarkedValues_allSeams :
    D.ProducedMarkedSeamEquations q hproper hmax hg P x b0 i0 := by
  have hs := D.markedCut_allSeams q (D.producedCutSeed q hg P x b0)
    (D.producedCutJ q hg P x b0 i0) (D.producedCutBand q hg P x b0 i0)
    (MatrixIso.unit (D.producedCutT q hg P x b0 i0)) hproper hmax (algebraMap R K)
    (D.refinedMarkedHandles q (D.producedCutBand q hg P x b0 i0).shape rfl
      (D.producedCutBand q hg P x b0 i0).rowRanks
      (D.producedCutBand q hg P x b0 i0).colRanks hproper hmax
      (D.bandCutRetainedHandles q (D.producedCutSeed q hg P x b0)
        (D.bandCutHandleT q hg P x)))
    (D.producedCutSeed_namedSeam q hg P x b0)
  have hJ : rebaseUnit (D.seamRank q).symm
      (D.bandCutChosenJ q (algebraMap R K) (D.producedCutSeed q hg P x b0) b0 i0
        (D.bandCutHandleA q hg P x)) = D.producedCutJ q hg P x b0 i0 := rfl
  have hT : rebaseUnit (D.seamRank q).symm
      (D.bandCutChosenT q (algebraMap R K) (D.producedCutSeed q hg P x b0) b0 i0
        (D.bandCutHandleT q hg P x)) = D.producedCutT q hg P x b0 i0 := rfl
  have hmirror := D.bandCutMirror_rebase q (D.producedCutSeed q hg P x b0)
    (D.bandCutChosenJ q (algebraMap R K) (D.producedCutSeed q hg P x b0) b0 i0
      (D.bandCutHandleA q hg P x))
    (D.bandCutChosenT q (algebraMap R K) (D.producedCutSeed q hg P x b0) b0 i0
      (D.bandCutHandleT q hg P x))
  simp only [hJ,hT] at hmirror
  have hside := congrArg₂
    (fun (J M : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
        (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ) =>
      D.refinedCutSideValues q (D.producedCutBand q hg P x b0 i0).shape rfl
        (D.producedCutBand q hg P x b0 i0).rowRanks
        (D.producedCutBand q hg P x b0 i0).colRanks
        (fun a => D.producedCutSeed q hg P x b0 (.side a)) J M) hJ hmirror
  have hv := congrArg
    (fun side : (D.refinedMarkedDiagram q (D.producedCutBand q hg P x b0 i0).shape rfl
      (D.producedCutBand q hg P x b0 i0).rowRanks
      (D.producedCutBand q hg P x b0 i0).colRanks hproper hmax).SideValues (R:=K) =>
      (D.refinedMarkedDiagram q (D.producedCutBand q hg P x b0 i0).shape rfl
      (D.producedCutBand q hg P x b0 i0).rowRanks
      (D.producedCutBand q hg P x b0 i0).colRanks hproper hmax).valuesFromPorts
        (D.markedCutFrames q (D.producedCutBand q hg P x b0 i0) hproper hmax
          (D.portFrame (D.producedCutSeed q hg P x b0))
          (MatrixIso.unit (D.producedCutT q hg P x b0 i0))) side
        (D.refinedMarkedHandles q (D.producedCutBand q hg P x b0 i0).shape rfl
          (D.producedCutBand q hg P x b0 i0).rowRanks
          (D.producedCutBand q hg P x b0 i0).colRanks hproper hmax
          (D.bandCutRetainedHandles q (D.producedCutSeed q hg P x b0)
            (D.bandCutHandleT q hg P x)))) hside
  unfold MarkedCutSeamFlag at hs
  have hc :=
    (D.refinedMarkedDiagram q (D.producedCutBand q hg P x b0 i0).shape rfl
      (D.producedCutBand q hg P x b0 i0).rowRanks
      (D.producedCutBand q hg P x b0 i0).colRanks hproper hmax).framedSeamEquations_of_values_eq
      (algebraMap R K) hv.symm hs
  unfold ProducedMarkedSeamEquations
  change ∀ s, FramedSeamEquation
    (D := D.producedMarkedDiagram q hproper hmax hg P x b0 i0)
    (φ := algebraMap R K) (g := D.producedMarkedValues q hproper hmax hg P x b0 i0) s
  exact hc

/-- The first short seam of the produced marked diagram. -/
lemma producedMarkedValues_firstShort :
    D.ProducedMarkedFirstShortEquation q hproper hmax hg P x b0 i0 := by
  exact D.producedMarkedValues_allSeams q hproper hmax hg P x b0 i0 _

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression HomTransport
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A] [Algebra R A]
    (D : Diagram F S V arity) (P : D.Punctures R)
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)

/-- Assemble a solution from its surface, seam, and vertex equations. -/
def solutionOfEquations
    (surface : ∀ f, (D.surfaceWord f).eval (algebraMap R A) g =
      (D.surfaceTarget P f).eval (algebraMap R A) g)
    (seam : ∀ s, SameFramedFlag (D.seamGrade s)
      (matrixUnitEquiv ((D.seamLeft s).eval (algebraMap R A) g))
      (matrixUnitEquiv ((D.seamRight s).eval (algebraMap R A) g)))
    (vertex : D.VertexHolds g) : D.Solution P A := by
  refine ⟨⟨g, ?_⟩, vertex⟩
  intro j
  cases j with
  | inl f =>
    change SameFramedFlag (fun _ => 0)
      (matrixUnitEquiv ((D.surfaceWord f).eval (algebraMap R A) g))
      (matrixUnitEquiv ((D.surfaceTarget P f).eval (algebraMap R A) g))
    rw [surface f]
    exact ⟨fun _ => rfl, fun _ _ _ => rfl⟩
  | inr s => exact seam s

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

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

def producedMarkedSolution
    (hb : D.boundarySide ⟨D.bandCutParent q,b0,i0⟩=⟨q,none⟩) :
    (D.producedMarkedDiagram q hproper hmax hg P x b0 i0).Solution
      (D.producedMarkedPunctures q hproper hmax hg P x b0 i0) K :=
  (D.producedMarkedDiagram q hproper hmax hg P x b0 i0).solutionOfEquations
    (D.producedMarkedPunctures q hproper hmax hg P x b0 i0)
    (D.producedMarkedValues q hproper hmax hg P x b0 i0)
    (D.producedMarkedValues_surface q hproper hmax hg P x b0 i0 hb)
    (D.producedMarkedValues_allSeams q hproper hmax hg P x b0 i0)
    (D.producedMarkedValues_vertexHolds q hproper hmax hg P x b0 i0)

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
