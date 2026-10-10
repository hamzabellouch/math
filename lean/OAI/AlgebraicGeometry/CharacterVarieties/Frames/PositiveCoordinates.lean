import OAI.AlgebraicGeometry.CharacterVarieties.Frames.MarkedFrames
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.SeamCoordinates
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.PortValues
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.SeamFactors

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
/-- Seam grades are independent of boundary enumeration. -/
private lemma lastShortSeamGrade_canonical {F S V : Type} {arity : S → ℕ}
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
    (Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (handle : (D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax).HandleValues (R:=K))
local notation "C" => D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax
local notation "FF" => D.markedCutFrames q w hproper hmax (D.portFrame g) T
local notation "C0" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "FF0" => D.namedCutPortFrames q w (D.portFrame g) T
private abbrev lastShortGeneratorValues :
    (e : (C).Generator) →
      (Matrix (Fin ((C).generatorRank e)) (Fin ((C).generatorRank e)) K)ˣ :=
  (C).valuesFromPorts (FF)
    (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks (fun a=>g (.side a)) J Y) handle
local notation "gg" => lastShortGeneratorValues (D := D) (q := q) (g := g)
  (J := J) (w := w) (T := T) (hproper := hproper) (hmax := hmax) (Y := Y) (handle := handle)
local notation "s" => D.cutOldSeam q w.shape q
local notation "oo" => D.ports.attach.symm (q,true)
private abbrev lastShortOldPort : LocalPort _ (C).ports.kind := ⟨.inl (oo).1,(oo).2⟩
private abbrev lastShortBandPort : LocalPort _ (C).ports.kind :=
  ⟨.inr (.inl (Fin.last w.shape.atomicBand.length)),
    Kind.output (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length))⟩
local notation "po" => lastShortOldPort (D := D) (q := q) (g := g) (J := J)
  (w := w) (hproper := hproper) (hmax := hmax)
local notation "pn" => lastShortBandPort (D := D) (q := q) (g := g) (J := J)
  (w := w) (hproper := hproper) (hmax := hmax)

/-- Child coordinates for the marked positive short seam. -/
def markedLastShortColumns : ((i : Fin (arity q)) × Fin (D.childDim q i)) ≃
    Fin ((C).seamDim (s)) := D.cutLastColumns q w

/-- Parent coordinates for the marked positive short seam. -/
def markedLastShortRows : Fin (D.rank (D.ports.facet ⟨q,none⟩)) ≃
    Fin ((C).seamDim (s)) := D.cutLastRows q w

/-- The terminal band port and the old positive port use the same seam columns. -/
def LastShortColumnsAligned : Prop :=
  ((D.cutLastNewActualColumns q w).trans ((C0).portColumnIndex (pn))).trans
      (finCongr (congrArg (C0).seamDim (congrArg Prod.fst (D.lastOriginalOutput_attach q w))))=
    D.cutLastColumns q w

lemma lastShortColumns_aligned : D.LastShortColumnsAligned q g J w hproper hmax := by
  change ((D.cutLastNewActualColumns q w).trans ((C0).portColumnIndex (pn))).trans
      (finCongr (congrArg (C0).seamDim (congrArg Prod.fst (D.lastOriginalOutput_attach q w))))=
    ((D.cutLastOldActualColumns q w).trans ((C0).portColumnIndex (po))).trans
      (finCongr (congrArg (C0).seamDim (congrArg Prod.fst (D.lastOldPositive_attach q w))))
  have h := (C0).common_portColumnIndex (po) (pn) (s) true false
    (D.lastOldPositive_attach q w) (D.lastOriginalOutput_attach q w)
    (D.lastAdjacentSame q w) (D.cutLastOldActualColumns q w) (D.cutLastNewActualColumns q w)
    (D.cutLastColumn_match q w)
  exact h

/-- The terminal band port and the old positive port use the same seam rows. -/
def LastShortRowsAligned : Prop :=
  ((D.cutLastNewActualRows q w).trans ((C0).portRowIndex (pn))).trans
      (finCongr (congrArg (C0).seamDim (congrArg Prod.fst (D.lastOriginalOutput_attach q w))))=
    D.cutLastRows q w

lemma lastShortRows_aligned : D.LastShortRowsAligned q g J w hproper hmax := by
  change ((D.cutLastNewActualRows q w).trans ((C0).portRowIndex (pn))).trans
      (finCongr (congrArg (C0).seamDim (congrArg Prod.fst (D.lastOriginalOutput_attach q w))))=
    ((D.cutLastOldActualRows q w).trans ((C0).portRowIndex (po))).trans
      (finCongr (congrArg (C0).seamDim (congrArg Prod.fst (D.lastOldPositive_attach q w))))
  have h := (C0).common_portRowIndex (po) (pn) (s) true false
    (D.lastOldPositive_attach q w) (D.lastOriginalOutput_attach q w)
    (D.lastAdjacentSame q w) (D.cutLastOldActualRows q w) (D.cutLastNewActualRows q w)
    (D.cutLastRow_match q w)
  exact h

/-- The positive short seam retains the grades of the original child coordinates. -/
def LastShortGrade : Prop :=
  ∀ i : (i : Fin (arity q)) × Fin (D.childDim q i),
    (C).seamGrade (s) (D.markedLastShortColumns q g J w hproper hmax i)=i.1.val

lemma lastShort_grade : D.LastShortGrade q g J w hproper hmax := by
  unfold LastShortGrade
  intro i
  rw [lastShortSeamGrade_canonical]
  exact D.cutLastColumns_grade q w i

/-- The unmarked endpoint frame has terminal band coordinates. -/
def LastShortCanonicalNewFrameCoordinates : Prop :=
  ((MatrixIso.unit ((C0).frameValues (FF0) (s) false)).reindex
    (D.cutLastColumns q w) (D.cutLastRows q w)).linearEquiv=w.lastFrame

lemma lastShortCanonicalNew_frameCoordinates
    (hc : D.LastShortColumnsAligned q g J w hproper hmax)
    (hr : D.LastShortRowsAligned q g J w hproper hmax) :
    D.LastShortCanonicalNewFrameCoordinates q g J w T := by
  unfold LastShortCanonicalNewFrameCoordinates
  unfold LastShortColumnsAligned at hc
  unfold LastShortRowsAligned at hr
  have hcoordinates := (C0).frameValues_coordinates (FF0) (pn) (s) false
    (D.lastOriginalOutput_attach q w)
    (D.cutLastNewActualColumns q w) (D.cutLastNewActualRows q w)
    (D.cutLastColumns q w) (D.cutLastRows q w) hc hr
  have hframe := D.cutLast_new_frameCoordinates q g w T
  unfold LastCutNewFrameCompatible at hframe
  exact hcoordinates.trans hframe

/-- The new endpoint frame has the terminal coordinates of the identified band. -/
def LastShortNewFrameCoordinates : Prop :=
  ∀ hh : (C).HandleValues (R:=K),
    ((MatrixIso.unit ((lastShortGeneratorValues (D := D) (q := q) (g := g) (J := J) (w := w) (T := T) (hproper := hproper) (hmax := hmax) (Y := Y) (handle := hh)) (.frame (s) false))).reindex
      (D.markedLastShortColumns q g J w hproper hmax) (D.markedLastShortRows q g J w hproper hmax)).linearEquiv=w.lastFrame

lemma lastShortNew_frameCoordinates :
    D.LastShortNewFrameCoordinates q g J w T hproper hmax Y := by
  unfold LastShortNewFrameCoordinates
  intro hh
  have hcanonical := valuesFromPorts_frameCoordinates_canonical (C) (FF)
    (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks
      (fun a=>g (.side a)) J Y) hh (s) false
    (D.markedLastShortColumns q g J w hproper hmax) (D.markedLastShortRows q g J w hproper hmax)
  have hframe := D.lastShortCanonicalNew_frameCoordinates q g J w T hproper hmax
    (D.lastShortColumns_aligned q g J w hproper hmax)
    (D.lastShortRows_aligned q g J w hproper hmax)
  unfold LastShortCanonicalNewFrameCoordinates at hframe
  exact hcanonical.trans hframe

/-- The old endpoint frame retains its named child coordinates. -/
def LastShortOldFrameCoordinates : Prop :=
  ∀ hh : (C).HandleValues (R:=K),
    ((MatrixIso.unit ((lastShortGeneratorValues (D := D) (q := q) (g := g) (J := J) (w := w) (T := T) (hproper := hproper) (hmax := hmax) (Y := Y) (handle := hh)) (.frame (s) true))).reindex
      (D.markedLastShortColumns q g J w hproper hmax) (D.markedLastShortRows q g J w hproper hmax)).linearEquiv=
        D.namedSeamFrame q (g (.frame q true))

lemma lastShortOld_frameCoordinates :
    D.LastShortOldFrameCoordinates q g J w T hproper hmax Y := by
  unfold LastShortOldFrameCoordinates
  intro hh
  have hcanonical := valuesFromPorts_frameCoordinates_canonical (C) (FF)
    (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks
      (fun a=>g (.side a)) J Y) hh (s) true
    (D.markedLastShortColumns q g J w hproper hmax) (D.markedLastShortRows q g J w hproper hmax)
  have hcoordinates := (C0).frameValues_coordinates (FF0) (po) (s) true
    (D.lastOldPositive_attach q w)
    (D.cutLastOldActualColumns q w) (D.cutLastOldActualRows q w)
    (D.cutLastColumns q w) (D.cutLastRows q w)
    rfl rfl
  have hframe := D.cutLast_old_frameCoordinates q g w T
  unfold LastCutOldFrameCompatible at hframe
  exact hcanonical.trans (hcoordinates.trans hframe)

/-- The parent transport of the positive short seam is the chosen cut matrix. -/
def LastShortParentCoordinates : Prop :=
  ∀ hh : (C).HandleValues (R:=K),
    ((MatrixIso.unit (((C).parentWord (s)).eval φ (lastShortGeneratorValues (D := D) (q := q) (g := g) (J := J) (w := w) (T := T) (hproper := hproper) (hmax := hmax) (Y := Y) (handle := hh)))).reindex
      (D.markedLastShortRows q g J w hproper hmax) (D.markedLastShortRows q g J w hproper hmax)).linearEquiv=(MatrixIso.unit J).linearEquiv

lemma lastShortParent_coordinates :
    D.LastShortParentCoordinates q g J w T hproper hmax φ Y := by
  intro hh
  exact (C).parentWord_coordinates (s) φ (lastShortGeneratorValues (D := D) (q := q) (g := g) (J := J) (w := w) (T := T) (hproper := hproper) (hmax := hmax) (Y := Y) (handle := hh))
    (D.cutOldSideRank q w.shape rfl w.rowRanks w.colRanks q none) J
    (D.refinedCutSideValues_last_parent q w.shape rfl w.rowRanks w.colRanks
      (fun a=>g (.side a)) J Y)
    (D.markedLastShortRows q g J w hproper hmax) (D.cutLastRows_finCongr q w)

/-- The ordered child inverse of the positive short seam retains its named coordinates. -/
def LastShortChildCoordinates : Prop :=
  ∀ hh : (C).HandleValues (R:=K),
    ((MatrixIso.unit ((Term.block ((C).childDim (s))
      (fun j => Term.inv ((C).childWord (s) j))).eval φ (lastShortGeneratorValues (D := D) (q := q) (g := g) (J := J) (w := w) (T := T) (hproper := hproper) (hmax := hmax) (Y := Y) (handle := hh)))).reindex
      (D.markedLastShortColumns q g J w hproper hmax) (D.markedLastShortColumns q g J w hproper hmax)).linearEquiv=D.namedChildInverse q g

lemma lastShortChild_coordinates :
    D.LastShortChildCoordinates q g J w T hproper hmax φ Y := by
  unfold LastShortChildCoordinates
  intro hh
  unfold namedChildInverse
  have h := valuesFromPorts_childWord_coordinates (C) (s) φ (FF)
    (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks
      (fun a=>g (.side a)) J Y) hh (D.childDim q)
    (finCongr (D.cutOldSeam_arity q w.shape q).symm)
    (fun i=>(D.cutOldSideRank q w.shape rfl w.rowRanks w.colRanks q (some i)).symm)
    (fun i=>g (.side ⟨q,some i⟩))
    (fun i=>D.refinedCutSideValues_old_child q w.shape rfl w.rowRanks w.colRanks
      (fun a=>g (.side a)) J Y q i)
    (D.markedLastShortColumns q g J w hproper hmax) (D.cutLastColumns_block q w)
  exact h

/-- The positive short seam preserves the framed flag equation of the original seam. -/
def MarkedLastShortFlag : Prop :=
  ∀ hh : (C).HandleValues (R:=K),
    SameFramedFlag (fun i : (i : Fin (arity q)) × Fin (D.childDim q i) => i.1.val)
      ((D.namedSeamFrame q (g (.frame q false))).trans (D.namedParentLinear q g))
      ((D.namedChildInverse q g).trans (D.namedSeamFrame q (g (.frame q true)))) →
    SameFramedFlag ((C).seamGrade (s))
      (matrixUnitEquiv (((C).seamLeft (s)).eval φ (lastShortGeneratorValues (D := D) (q := q) (g := g) (J := J) (w := w) (T := T) (hproper := hproper) (hmax := hmax) (Y := Y) (handle := hh))))
      (matrixUnitEquiv (((C).seamRight (s)).eval φ (lastShortGeneratorValues (D := D) (q := q) (g := g) (J := J) (w := w) (T := T) (hproper := hproper) (hmax := hmax) (Y := Y) (handle := hh))))

/-- Coordinates of the positive short seam's complete left word. -/
def LastShortLeftWordCoordinates : Prop :=
  ∀ hh : (C).HandleValues (R:=K),
    ((MatrixIso.unit (((C).seamLeft (s)).eval φ
      (lastShortGeneratorValues (D := D) (q := q) (g := g) (J := J)
        (w := w) (T := T) (hproper := hproper) (hmax := hmax) (Y := Y) (handle := hh)))).reindex
      (D.markedLastShortColumns q g J w hproper hmax)
      (D.markedLastShortRows q g J w hproper hmax)).linearEquiv=
        w.lastFrame.trans (MatrixIso.unit J).linearEquiv

lemma lastShort_leftWordCoordinates
    (hx : D.LastShortNewFrameCoordinates q g J w T hproper hmax Y)
    (hp : D.LastShortParentCoordinates q g J w T hproper hmax φ Y) :
    D.LastShortLeftWordCoordinates q g J w T hproper hmax φ Y := by
  unfold LastShortLeftWordCoordinates
  intro hh
  unfold LastShortNewFrameCoordinates at hx
  unfold LastShortParentCoordinates at hp
  apply (C).seamLeft_coordinates (s) φ
    (lastShortGeneratorValues (D := D) (q := q) (g := g) (J := J)
      (w := w) (T := T) (hproper := hproper) (hmax := hmax) (Y := Y) (handle := hh))
    (D.markedLastShortColumns q g J w hproper hmax)
    (D.markedLastShortRows q g J w hproper hmax)
    w.lastFrame (MatrixIso.unit J).linearEquiv
  · exact hx hh
  · exact hp hh

/-- Coordinates of the positive short seam's complete right word. -/
def LastShortRightWordCoordinates : Prop :=
  ∀ hh : (C).HandleValues (R:=K),
    ((MatrixIso.unit (((C).seamRight (s)).eval φ
      (lastShortGeneratorValues (D := D) (q := q) (g := g) (J := J)
        (w := w) (T := T) (hproper := hproper) (hmax := hmax) (Y := Y) (handle := hh)))).reindex
      (D.markedLastShortColumns q g J w hproper hmax)
      (D.markedLastShortRows q g J w hproper hmax)).linearEquiv=
        (D.namedChildInverse q g).trans (D.namedSeamFrame q (g (.frame q true)))

lemma lastShort_rightWordCoordinates
    (hy : D.LastShortOldFrameCoordinates q g J w T hproper hmax Y)
    (hu : D.LastShortChildCoordinates q g J w T hproper hmax φ Y) :
    D.LastShortRightWordCoordinates q g J w T hproper hmax φ Y := by
  unfold LastShortRightWordCoordinates
  intro hh
  unfold LastShortOldFrameCoordinates at hy
  unfold LastShortChildCoordinates at hu
  apply (C).seamRight_coordinates (s) φ
    (lastShortGeneratorValues (D := D) (q := q) (g := g) (J := J)
      (w := w) (T := T) (hproper := hproper) (hmax := hmax) (Y := Y) (handle := hh))
    (D.markedLastShortColumns q g J w hproper hmax)
    (D.markedLastShortRows q g J w hproper hmax)
    (D.namedSeamFrame q (g (.frame q true))) (D.namedChildInverse q g)
  · exact hy hh
  · exact hu hh

lemma markedLastShortFlag_of_word_coordinates
    (ha : D.LastShortGrade q g J w hproper hmax)
    (hl : D.LastShortLeftWordCoordinates q g J w T hproper hmax φ Y)
    (hr : D.LastShortRightWordCoordinates q g J w T hproper hmax φ Y) :
    D.MarkedLastShortFlag q g J w T hproper hmax φ Y := by
  unfold MarkedLastShortFlag
  intro hh hold
  unfold LastShortGrade at ha
  unfold LastShortLeftWordCoordinates at hl
  unfold LastShortRightWordCoordinates at hr
  have hband := NamedBandGrades.cut_short_last (D.childDim q)
    (D.namedSeamFrame q (g (.frame q false))) (D.namedSeamFrame q (g (.frame q true)))
    (D.namedParentLinear q g) (MatrixIso.unit J).linearEquiv
    (D.namedChildInverse q g) w hold
  apply (C).seamHolds_of_wordCoordinates (s) φ
    (lastShortGeneratorValues (D := D) (q := q) (g := g) (J := J)
      (w := w) (T := T) (hproper := hproper) (hmax := hmax) (Y := Y) (handle := hh))
    (D.markedLastShortColumns q g J w hproper hmax)
    (D.markedLastShortRows q g J w hproper hmax)
    (fun i : (i : Fin (arity q)) × Fin (D.childDim q i) => i.1.val)
    (w.lastFrame.trans (MatrixIso.unit J).linearEquiv)
    ((D.namedChildInverse q g).trans (D.namedSeamFrame q (g (.frame q true))))
  · exact ha
  · exact hl hh
  · exact hr hh
  · exact hband

lemma markedLastShort_seamHolds :
    D.MarkedLastShortFlag q g J w T hproper hmax φ Y := by
  have hl := D.lastShort_leftWordCoordinates q g J w T hproper hmax φ Y
    (D.lastShortNew_frameCoordinates q g J w T hproper hmax Y)
    (D.lastShortParent_coordinates q g J w T hproper hmax φ Y)
  have hr := D.lastShort_rightWordCoordinates q g J w T hproper hmax φ Y
    (D.lastShortOld_frameCoordinates q g J w T hproper hmax Y)
    (D.lastShortChild_coordinates q g J w T hproper hmax φ Y)
  exact D.markedLastShortFlag_of_word_coordinates q g J w T hproper hmax φ Y
    (D.lastShort_grade q g J w hproper hmax) hl hr

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
