import OAI.AlgebraicGeometry.CharacterVarieties.Seams.PortEquations
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.BoundaryMarking

namespace OAI

/-!
# Internal seams of a marked cut

Original, reflected, and transverse branches retain their framed seam equations
when the boundary enumeration is marked.
-/

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K R : Type} {arity : S → ℕ} [Field K] [CommRing R]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h) (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (φ : R →+* K) (side : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
local notation "C" => D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax
local notation "FF" => D.markedCutFrames q w hproper hmax old T
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)

/-- The original internal seams satisfy their framed flag equations for every handle value. -/
def MarkedOriginalSeams : Prop :=
  ∀ (handle : (C).HandleValues (R:=K)) (k : Fin w.shape.atomicBand.length),
    let gg := valuesFromPorts (C) (FF)
      (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handle
    SameFramedFlag ((C).seamGrade (BandGraft.originalPort (A) q (B) k.succ true))
      (matrixUnitEquiv (((C).seamLeft (BandGraft.originalPort (A) q (B) k.succ true)).eval φ gg))
      (matrixUnitEquiv (((C).seamRight (BandGraft.originalPort (A) q (B) k.succ true)).eval φ gg))

lemma markedOriginal_seamHolds : D.MarkedOriginalSeams q w old T hproper hmax φ side J Y := by
  intro handle k
  have hs := D.refinedCutSideValues_original_succ q w.shape rfl w.rowRanks w.colRanks side J Y
  unfold OriginalInternalSideValuesTrivial at hs
  have hi := D.origFrameValues_eq q w old T k
  unfold OriginalFrameValuesAgree at hi
  have hf := (D.marked_frameValues q w.shape rfl w.rowRanks w.colRanks hproper hmax
      (D.namedCutPortFrames q w old T) (BandGraft.originalPort (A) q (B) k.succ true) false).trans
    (hi.trans (D.marked_frameValues q w.shape rfl w.rowRanks w.colRanks hproper hmax
      (D.namedCutPortFrames q w old T) (BandGraft.originalPort (A) q (B) k.succ true) true).symm)
  have result := (C).valuesFromPorts_trivialSides_seamHolds φ (FF)
    (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handle
    (BandGraft.originalPort (A) q (B) k.succ true) (hs k) hf
  exact result

/-- The reflected internal seams satisfy their framed flag equations for every handle value. -/
def MarkedMirrorSeams : Prop :=
  ∀ (handle : (C).HandleValues (R:=K)) (k : Fin w.shape.atomicBand.length),
    let gg := valuesFromPorts (C) (FF)
      (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handle
    SameFramedFlag ((C).seamGrade (BandGraft.mirrorOutput (A) q (B) k.castSucc))
      (matrixUnitEquiv (((C).seamLeft (BandGraft.mirrorOutput (A) q (B) k.castSucc)).eval φ gg))
      (matrixUnitEquiv (((C).seamRight (BandGraft.mirrorOutput (A) q (B) k.castSucc)).eval φ gg))

lemma markedMirror_seamHolds : D.MarkedMirrorSeams q w old T hproper hmax φ side J Y := by
  intro handle k
  have hs := D.refinedCutSideValues_mirror_castSucc q w.shape rfl w.rowRanks w.colRanks side J Y
  unfold MirrorInternalSideValuesTrivial at hs
  have hi := D.mirrorFrameValues_eq q w old T k
  unfold MirrorFrameValuesAgree at hi
  have hf := (D.marked_frameValues q w.shape rfl w.rowRanks w.colRanks hproper hmax
      (D.namedCutPortFrames q w old T) (BandGraft.mirrorOutput (A) q (B) k.castSucc) false).trans
    (hi.trans (D.marked_frameValues q w.shape rfl w.rowRanks w.colRanks hproper hmax
      (D.namedCutPortFrames q w old T) (BandGraft.mirrorOutput (A) q (B) k.castSucc) true).symm)
  have result := (C).valuesFromPorts_trivialSides_seamHolds φ (FF)
    (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handle
    (BandGraft.mirrorOutput (A) q (B) k.castSucc) (hs k) hf
  exact result

/-- The positive transverse seams satisfy their framed flag equations for every handle value. -/
def MarkedPositiveBranchSeams : Prop :=
  ∀ (handle : (C).HandleValues (R:=K)) (k : BandGraft.PositiveBranch (A) q (B)),
    let gg := valuesFromPorts (C) (FF)
      (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handle
    SameFramedFlag ((C).seamGrade (BandGraft.branchPlus (A) q (B) k))
      (matrixUnitEquiv (((C).seamLeft (BandGraft.branchPlus (A) q (B) k)).eval φ gg))
      (matrixUnitEquiv (((C).seamRight (BandGraft.branchPlus (A) q (B) k)).eval φ gg))

lemma markedPositiveBranch_seamHolds : D.MarkedPositiveBranchSeams q w old T hproper hmax φ side J Y := by
  intro handle k
  have hs := D.refinedCutSideValues_branchPos q w.shape rfl w.rowRanks w.colRanks side J Y
  unfold PositiveBranchSideValuesTrivial at hs
  have hi := D.branchPosFrameValues_eq q w k old T
  unfold PositiveBranchFrameValuesAgree at hi
  have hf := (D.marked_frameValues q w.shape rfl w.rowRanks w.colRanks hproper hmax
      (D.namedCutPortFrames q w old T) (BandGraft.branchPlus (A) q (B) k) false).trans
    (hi.trans (D.marked_frameValues q w.shape rfl w.rowRanks w.colRanks hproper hmax
      (D.namedCutPortFrames q w old T) (BandGraft.branchPlus (A) q (B) k) true).symm)
  have result := (C).valuesFromPorts_trivialSides_seamHolds φ (FF)
    (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handle
    (BandGraft.branchPlus (A) q (B) k) (hs k) hf
  exact result

/-- The negative transverse seams satisfy their framed flag equations for every handle value. -/
def MarkedNegativeBranchSeams : Prop :=
  ∀ (handle : (C).HandleValues (R:=K)) (k : BandGraft.NegativeBranch (A) q (B)),
    let gg := valuesFromPorts (C) (FF)
      (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handle
    SameFramedFlag ((C).seamGrade (BandGraft.branchNegPlus (A) q (B) k))
      (matrixUnitEquiv (((C).seamLeft (BandGraft.branchNegPlus (A) q (B) k)).eval φ gg))
      (matrixUnitEquiv (((C).seamRight (BandGraft.branchNegPlus (A) q (B) k)).eval φ gg))

lemma markedNegativeBranch_seamHolds : D.MarkedNegativeBranchSeams q w old T hproper hmax φ side J Y := by
  intro handle k
  have hs := D.refinedCutSideValues_branchNeg q w.shape rfl w.rowRanks w.colRanks side J Y
  unfold NegativeBranchSideValuesTrivial at hs
  have hi := D.branchNegFrameValues_eq q w k old T
  unfold NegativeBranchFrameValuesAgree at hi
  have hf := (D.marked_frameValues q w.shape rfl w.rowRanks w.colRanks hproper hmax
      (D.namedCutPortFrames q w old T) (BandGraft.branchNegPlus (A) q (B) k) false).trans
    (hi.trans (D.marked_frameValues q w.shape rfl w.rowRanks w.colRanks hproper hmax
      (D.namedCutPortFrames q w old T) (BandGraft.branchNegPlus (A) q (B) k) true).symm)
  have result := (C).valuesFromPorts_trivialSides_seamHolds φ (FF)
    (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handle
    (BandGraft.branchNegPlus (A) q (B) k) (hs k) hf
  exact result

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
