import OAI.AlgebraicGeometry.CharacterVarieties.Frames.MirrorSeamCoordinates
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.SeamFactors

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
/-- Seam grades are independent of boundary enumeration. -/
private lemma mirrorSeamGrade_canonical {F S V : Type} {arity : S → ℕ}
    [Finite S] (D : Diagram F S V arity) (s : S) (i : Fin (D.seamDim s)) :
    D.seamGrade s i=
      (SurfacePresentation.fromPorts D.ports D.rank D.genus D.seamRank).seamGrade s i := rfl

variable {F S V K R : Type} {arity : S → ℕ} [Field K] [CommRing R]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (J : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (w : IdentifiedBand (D.childDim q) (D.namedSeamFrame q (g (.frame q false)))
      (((D.namedSeamFrame q (g (.frame q false))).trans (D.namedParentLinear q g)).trans
        (MatrixIso.unit J).linearEquiv.symm))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (φ : R →+* K)
local notation "C" => D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax

/-- Column coordinates of the marked short mirror seam. -/
def markedMirrorColumns : ((i : Fin (arity q)) × Fin (D.childDim q i)) ≃
    Fin ((C).seamDim (D.cutShortSeam q w.shape true)) := D.cutMirrorSeamColumns q w

/-- Row coordinates of the marked short mirror seam. -/
def markedMirrorRows : Fin (D.rank (D.ports.facet ⟨q,none⟩)) ≃
    Fin ((C).seamDim (D.cutShortSeam q w.shape true)) := D.cutMirrorSeamRows q w

/-- The marked short mirror seam has the original child-index grading. -/
def MarkedMirrorGrade : Prop :=
  ∀ i : (i : Fin (arity q)) × Fin (D.childDim q i),
    (C).seamGrade (D.cutShortSeam q w.shape true)
      (D.markedMirrorColumns q g J w hproper hmax i)=i.1.val

lemma markedMirror_grade : D.MarkedMirrorGrade q g J w hproper hmax := by
  unfold MarkedMirrorGrade
  intro i
  rw [mirrorSeamGrade_canonical]
  exact D.cutMirrorSeamColumns_grade q w i

/-- The short mirror seam satisfies the framed flag equation. -/
def MarkedMirrorShortFlags : Prop :=
  ∀ hh : (C).HandleValues (R:=K),
    SameFramedFlag ((C).seamGrade (D.cutShortSeam q w.shape true))
      (matrixUnitEquiv (((C).seamLeft (D.cutShortSeam q w.shape true)).eval φ
        (mirrorShortGeneratorValues (D := D) (q := q) (g := g) (J := J) (w := w)
          (T := T) (hproper := hproper) (hmax := hmax) (handle := hh))))
      (matrixUnitEquiv (((C).seamRight (D.cutShortSeam q w.shape true)).eval φ
        (mirrorShortGeneratorValues (D := D) (q := q) (g := g) (J := J) (w := w)
          (T := T) (hproper := hproper) (hmax := hmax) (handle := hh))))

/-- Coordinates of the complete left word of the short mirror seam. -/
def MirrorLeftWordCoordinates : Prop :=
  ∀ hh : (C).HandleValues (R:=K),
    ((MatrixIso.unit (((C).seamLeft (D.cutShortSeam q w.shape true)).eval φ
      (mirrorShortGeneratorValues (D := D) (q := q) (g := g) (J := J) (w := w)
        (T := T) (hproper := hproper) (hmax := hmax) (handle := hh)))).reindex
      (D.markedMirrorColumns q g J w hproper hmax) (D.markedMirrorRows q g J w hproper hmax)).linearEquiv=
        (w.mirrorFirstFrame T).trans
          (cutInnerLinear (D.namedParentLinear q g) (MatrixIso.unit J).linearEquiv T)

lemma mirrorLeft_wordCoordinates
    (hx : D.MirrorFirstFrameCoordinates q g J w T hproper hmax)
    (hp : D.MirrorParentCoordinates q g J w T hproper hmax φ) :
    D.MirrorLeftWordCoordinates q g J w T hproper hmax φ := by
  unfold MirrorLeftWordCoordinates
  intro hh
  unfold MirrorFirstFrameCoordinates at hx
  unfold MirrorParentCoordinates at hp
  apply (C).seamLeft_coordinates (D.cutShortSeam q w.shape true) φ
    (mirrorShortGeneratorValues (D := D) (q := q) (g := g) (J := J) (w := w)
        (T := T) (hproper := hproper) (hmax := hmax) (handle := hh))
    (D.markedMirrorColumns q g J w hproper hmax) (D.markedMirrorRows q g J w hproper hmax)
    (w.mirrorFirstFrame T)
    (cutInnerLinear (D.namedParentLinear q g) (MatrixIso.unit J).linearEquiv T)
  · exact hx hh
  · exact hp hh

/-- Coordinates of the complete right word of the short mirror seam. -/
def MirrorRightWordCoordinates : Prop :=
  ∀ hh : (C).HandleValues (R:=K),
    ((MatrixIso.unit (((C).seamRight (D.cutShortSeam q w.shape true)).eval φ
      (mirrorShortGeneratorValues (D := D) (q := q) (g := g) (J := J) (w := w)
        (T := T) (hproper := hproper) (hmax := hmax) (handle := hh)))).reindex
      (D.markedMirrorColumns q g J w hproper hmax) (D.markedMirrorRows q g J w hproper hmax)).linearEquiv=
        (LinearEquiv.refl K (((i : Fin (arity q)) × Fin (D.childDim q i)) → K)).trans
          (w.mirrorLastFrame T)

lemma mirrorRight_wordCoordinates
    (hy : D.MirrorLastFrameCoordinates q g J w T hproper hmax)
    (hu : D.MirrorChildCoordinates q g J w T hproper hmax φ) :
    D.MirrorRightWordCoordinates q g J w T hproper hmax φ := by
  unfold MirrorRightWordCoordinates
  intro hh
  unfold MirrorLastFrameCoordinates at hy
  unfold MirrorChildCoordinates at hu
  apply (C).seamRight_coordinates (D.cutShortSeam q w.shape true) φ
    (mirrorShortGeneratorValues (D := D) (q := q) (g := g) (J := J) (w := w)
      (T := T) (hproper := hproper) (hmax := hmax) (handle := hh))
    (D.markedMirrorColumns q g J w hproper hmax) (D.markedMirrorRows q g J w hproper hmax)
    (w.mirrorLastFrame T)
    (LinearEquiv.refl K (((i : Fin (arity q)) × Fin (D.childDim q i)) → K))
  · exact hy hh
  · exact hu hh


lemma markedMirrorShortFlags_of_wordCoordinates
    (ha : D.MarkedMirrorGrade q g J w hproper hmax)
    (hl : D.MirrorLeftWordCoordinates q g J w T hproper hmax φ)
    (hr : D.MirrorRightWordCoordinates q g J w T hproper hmax φ) :
    D.MarkedMirrorShortFlags q g J w T hproper hmax φ := by
  unfold MarkedMirrorShortFlags
  intro hh
  unfold MarkedMirrorGrade at ha
  unfold MirrorLeftWordCoordinates at hl
  unfold MirrorRightWordCoordinates at hr
  have hband0 := NamedBandGrades.cut_short_mirror (D.childDim q)
    (D.namedSeamFrame q (g (.frame q false))) (D.namedParentLinear q g)
    (MatrixIso.unit J).linearEquiv T w
  have hband : SameFramedFlag
      (fun i : (i : Fin (arity q)) × Fin (D.childDim q i) => i.1.val)
      ((w.mirrorFirstFrame T).trans
        (cutInnerLinear (D.namedParentLinear q g) (MatrixIso.unit J).linearEquiv T))
      ((LinearEquiv.refl K (((i : Fin (arity q)) × Fin (D.childDim q i)) → K)).trans
        (w.mirrorLastFrame T)) := by
    simp only [LinearEquiv.refl_trans]
    convert! hband0 using 1
  apply (C).seamHolds_of_wordCoordinates (D.cutShortSeam q w.shape true) φ
    (mirrorShortGeneratorValues (D := D) (q := q) (g := g) (J := J) (w := w)
        (T := T) (hproper := hproper) (hmax := hmax) (handle := hh))
    (D.markedMirrorColumns q g J w hproper hmax) (D.markedMirrorRows q g J w hproper hmax)
    (fun i : (i : Fin (arity q)) × Fin (D.childDim q i) => i.1.val)
    ((w.mirrorFirstFrame T).trans
      (cutInnerLinear (D.namedParentLinear q g) (MatrixIso.unit J).linearEquiv T))
    ((LinearEquiv.refl K (((i : Fin (arity q)) × Fin (D.childDim q i)) → K)).trans
      (w.mirrorLastFrame T))
  · exact ha
  · exact hl hh
  · exact hr hh
  · exact hband

lemma markedMirrorShort_seamHolds :
    D.MarkedMirrorShortFlags q g J w T hproper hmax φ := by
  have hl := D.mirrorLeft_wordCoordinates q g J w T hproper hmax φ
    (D.mirrorFirst_frameCoordinates q g J w T hproper hmax)
    (D.mirrorParent_coordinates q g J w T hproper hmax φ)
  have hr := D.mirrorRight_wordCoordinates q g J w T hproper hmax φ
    (D.mirrorLast_frameCoordinates q g J w T hproper hmax)
    (D.mirrorChild_coordinates q g J w T hproper hmax φ)
  exact D.markedMirrorShortFlags_of_wordCoordinates q g J w T hproper hmax φ
    (D.markedMirror_grade q g J w hproper hmax) hl hr

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
