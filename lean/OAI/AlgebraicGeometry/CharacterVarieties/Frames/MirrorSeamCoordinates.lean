import OAI.AlgebraicGeometry.CharacterVarieties.Frames.PortValues
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.MarkedFrames
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.FramedFlags
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.SeamCoordinates
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.MirrorCoordinates

namespace OAI


noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)

/-- The final mirror output belongs to the final end of the short mirror seam. -/
def CutMirrorLastOutputAttached : Prop :=
    (C).ports.attach ⟨.inr (.inr (Fin.last w.shape.atomicBand.length)),
      (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorPort
        (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output⟩=
      (D.cutShortSeam q w.shape true,true)

lemma cutMirrorLastOutput_attach : D.CutMirrorLastOutputAttached q w := by
  exact (BandGraft.wiring (A) q (B)).endOf_portAt
    (BandGraft.mirrorOutput (A) q (B) (Fin.last w.shape.atomicBand.length),true)

def cutMirrorSeamColumns : ((i : Fin (arity q)) × Fin (D.childDim q i)) ≃
    Fin ((C).seamDim (D.cutShortSeam q w.shape true)) :=
  (Equiv.sigmaCongr (finCongr (D.cutShortSeam_arity q w.shape true).symm)
    (fun i => finCongr (D.cutShortSideRank q w.shape rfl w.rowRanks w.colRanks true (some i)).symm)).trans
      (blockIndex ((C).childDim (D.cutShortSeam q w.shape true))).symm

def cutMirrorSeamRows : Fin (D.rank (D.ports.facet ⟨q,none⟩)) ≃
    Fin ((C).seamDim (D.cutShortSeam q w.shape true)) :=
  finCongr ((D.cutShortSideRank q w.shape rfl w.rowRanks w.colRanks true none).symm.trans
    ((C).seamRank (D.cutShortSeam q w.shape true)))

variable (v : Fin (w.shape.atomicBand.length+1)) (p : (w.shape.atomicBand.kind v).table.Port)
    (e : ((i : Fin (arity q)) × Fin (D.childDim q i)) ≃ (w.shape.vertexAtoms v).localRanks.Columns p)
    (hr : (w.shape.vertexAtoms v).rank ⟨p,none⟩=D.rank (D.ports.facet ⟨q,none⟩))
    (b : Bool)

/-- Mirror column coordinates agree with the short-seam enumeration. -/
def CutMirrorSeamColumnsCoordinates : Prop :=
  ∀ (ha : (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks).ports.attach
      ⟨.inr (.inr v),(w.shape.atomicBand.kind v).mirrorPort p⟩ =
      (D.cutShortSeam q w.shape true,b)),
    (∀ i,((w.shape.atomicBand.kind v).childEnumeration p (e i).1).val=i.1.val) →
    (∀ i,(e i).2.val=i.2.val) →
    (C).columnsAt ⟨.inr (.inr v),(w.shape.atomicBand.kind v).mirrorPort p⟩
      (D.cutShortSeam q w.shape true) b ha (D.cutMirrorActualColumns q w v p e)=
      D.cutMirrorSeamColumns q w

lemma cutMirrorSeamColumns_coordinates :
    D.CutMirrorSeamColumnsCoordinates q w v p e b := by
  intro ha he hv
  apply (C).port_coordinates_blockIndex (D.childDim q) _ _ b ha
    (finCongr (D.cutShortSeam_arity q w.shape true).symm)
    (fun i=>(D.cutShortSideRank q w.shape rfl w.rowRanks w.colRanks true (some i)).symm)
    (D.cutMirrorActualColumns q w v p e)
  · intro i
    exact (D.cutMirrorActualColumns_childEnumeration q w v p e i).trans (he i)
  · intro i
    exact (D.cutMirrorActualColumns_value q w v p e i).trans (hv i)

/-- Mirror row coordinates agree with the short-seam enumeration. -/
def CutMirrorSeamRowsCoordinates : Prop :=
  ∀ (ha : (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks).ports.attach
      ⟨.inr (.inr v),(w.shape.atomicBand.kind v).mirrorPort p⟩ =
      (D.cutShortSeam q w.shape true,b)),
    (C).rowsAt ⟨.inr (.inr v),(w.shape.atomicBand.kind v).mirrorPort p⟩
      (D.cutShortSeam q w.shape true) b ha (D.cutMirrorActualRows q w v p hr)=
      D.cutMirrorSeamRows q w

lemma cutMirrorSeamRows_coordinates :
    D.CutMirrorSeamRowsCoordinates q w v p hr b := by
  intro ha
  apply Equiv.ext
  intro i
  apply Fin.ext
  rfl

/-- The short mirror seam grading is the original child index. -/
def CutMirrorSeamGrade : Prop :=
  ∀ (i : (i : Fin (arity q)) × Fin (D.childDim q i)),
    (C).seamGrade (D.cutShortSeam q w.shape true) (D.cutMirrorSeamColumns q w i)=i.1.val

lemma cutMirrorSeamColumns_grade : D.CutMirrorSeamGrade q w := by
  intro i
  exact (C).seamGrade_common (D.childDim q) (D.cutShortSeam q w.shape true)
    (finCongr (D.cutShortSeam_arity q w.shape true).symm)
    (fun j=>(D.cutShortSideRank q w.shape rfl w.rowRanks w.colRanks true (some j)).symm)
    (D.cutMirrorSeamColumns q w) rfl (fun _=>rfl) i
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {K : Type} [CommRing K] {n : ℕ}
lemma blockUnitOne_linear (d : Fin n → ℕ) :
    (MatrixIso.block (fun i => MatrixIso.unit (1 : (Matrix (Fin (d i)) (Fin (d i)) K)ˣ)⁻¹)).linearEquiv=
      LinearEquiv.refl K (((i : Fin n) × Fin (d i)) → K) := by
  let : DecidableEq (Fin n) := Classical.decEq _
  simp only [inv_one]
  ext v i
  simp only [MatrixIso.linearEquiv,MatrixIso.block,MatrixIso.unit,
    Matrix.toLin'_apply,Units.val_one,LinearEquiv.coe_mk,LinearEquiv.refl_apply]
  erw [Matrix.blockDiagonal'_one,Matrix.one_mulVec]
end IntegralCharacterVarieties.MatrixIso

noncomputable section
namespace IntegralCharacterVarieties.MatrixIso
open scoped Classical Matrix
variable {K : Type} [Field K] {n r : ℕ}
lemma cutInnerUnit_linear (P J : (Matrix (Fin r) (Fin r) K)ˣ)
    (T : MatrixIso K (Fin r) (Fin r)) :
    (MatrixIso.unit (T.toUnit⁻¹*J⁻¹*P*T.toUnit)).linearEquiv=
      NamedBandGrades.cutInnerLinear (MatrixIso.unit P).linearEquiv (MatrixIso.unit J).linearEquiv T := by
  simp only [MatrixIso.unit_mul,MatrixIso.unit_inv,MatrixIso.unit_toUnit,
    MatrixIso.linearEquiv_trans_eq,NamedBandGrades.cutInnerLinear]
  ext v i
  rfl

end IntegralCharacterVarieties.MatrixIso
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
/-- Parent coordinates for values induced by ports and side transports. -/
private lemma mirrorParentWord_coordinates
    {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K]
    (D : Diagram F S V arity) (s : S) (φ : R →+* K)
    (frames : D.PortFrames (R:=K)) (side : D.SideValues (R:=K))
    (handle : D.HandleValues (R:=K)) {n : ℕ}
    (h : D.rank (D.ports.facet ⟨s,none⟩)=n)
    (p : (Matrix (Fin n) (Fin n) K)ˣ)
    (hp : rebaseUnit h (side ⟨s,none⟩)=p)
    (e : Fin n ≃ Fin (D.seamDim s))
    (he : e=finCongr (h.symm.trans (D.seamRank s))) :
    ((MatrixIso.unit ((D.parentWord s).eval φ
      (D.valuesFromPorts frames side handle))).reindex e e).linearEquiv=
        (MatrixIso.unit p).linearEquiv := by
  exact D.parentWord_coordinates s φ (D.valuesFromPorts frames side handle) h p hp e he

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
    (handle : (D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax).HandleValues (R:=K))
local notation "C" => D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax
local notation "FF" => D.markedCutFrames q w hproper hmax (D.portFrame g) T
local notation "C0" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "FF0" => D.namedCutPortFrames q w (D.portFrame g) T
abbrev mirrorInnerTransport :
    (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ :=
  T.toUnit⁻¹ * J⁻¹ *
    (show (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ from g (.side ⟨q,none⟩)) * T.toUnit
local notation "Y" => mirrorInnerTransport (D := D) (q := q) (g := g) (J := J) (T := T)
abbrev mirrorShortGeneratorValues :
    (e : (C).Generator) →
      (Matrix (Fin ((C).generatorRank e)) (Fin ((C).generatorRank e)) K)ˣ :=
  (C).valuesFromPorts (FF)
    (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks (fun a=>g (.side a)) J (Y)) handle
local notation "gg" => mirrorShortGeneratorValues (D := D) (q := q) (g := g)
  (J := J) (w := w) (T := T) (hproper := hproper) (hmax := hmax) (handle := handle)

/-- The initial mirror frame has the first coordinates of the identified band. -/
def MirrorFirstFrameCoordinates : Prop :=
  ∀ hh : (C).HandleValues (R:=K),
    ((MatrixIso.unit ((mirrorShortGeneratorValues (D := D) (q := q) (g := g) (J := J) (w := w) (T := T) (hproper := hproper) (hmax := hmax) (handle := hh)) (.frame (D.cutShortSeam q w.shape true) false))).reindex
      (D.cutMirrorSeamColumns q w) (D.cutMirrorSeamRows q w)).linearEquiv=w.mirrorFirstFrame T

lemma mirrorFirst_frameCoordinates :
    D.MirrorFirstFrameCoordinates q g J w T hproper hmax := by
  intro hh
  have hcanonical := valuesFromPorts_frameCoordinates_canonical (C) (FF)
    (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks (fun a => g (.side a)) J (Y))
    hh (D.cutShortSeam q w.shape true) false
    (D.cutMirrorSeamColumns q w) (D.cutMirrorSeamRows q w)
  have hcoordinates := (C0).frameValues_coordinates (FF0)
    ⟨.inr (.inr 0),(w.shape.atomicBand.kind 0).mirrorPort (w.shape.atomicBand.kind 0).input⟩
    (D.cutShortSeam q w.shape true) false (D.mirrorFirstInput_attach q w)
    (D.cutMirrorActualColumns q w 0 (w.shape.atomicBand.kind 0).input w.firstColumns.symm)
    (D.cutMirrorActualRows q w 0 (w.shape.atomicBand.kind 0).input w.firstParent_rank)
    (D.cutMirrorSeamColumns q w) (D.cutMirrorSeamRows q w)
    (D.cutMirrorSeamColumns_coordinates q w 0 (w.shape.atomicBand.kind 0).input w.firstColumns.symm false
      (D.mirrorFirstInput_attach q w)
      (by
        intro i
        change ((w.shape.atomicBand.kind 0).childEnumeration (w.shape.atomicBand.kind 0).input (w.firstChild.symm i.1)).val=i.1.val
        simp only [IdentifiedBand.firstChild,Equiv.symm_trans_apply,Equiv.apply_symm_apply]
        rfl)
      (sigmaFinCongr_symm_val (m := D.childDim q) w.firstChild w.firstChild_rank))
    (D.cutMirrorSeamRows_coordinates q w 0 (w.shape.atomicBand.kind 0).input w.firstParent_rank false
      (D.mirrorFirstInput_attach q w))
  have hframe := D.cutMirror_frameCoordinates q w 0 (w.shape.atomicBand.kind 0).input w.firstColumns.symm w.firstParent_rank
      (D.portFrame g) T
  unfold CutMirrorFrameCoordinates at hframe
  exact hcanonical.trans (hcoordinates.trans hframe)

/-- The terminal mirror frame has the last coordinates of the identified band. -/
def MirrorLastFrameCoordinates : Prop :=
  ∀ hh : (C).HandleValues (R:=K),
    ((MatrixIso.unit ((mirrorShortGeneratorValues (D := D) (q := q) (g := g) (J := J) (w := w) (T := T) (hproper := hproper) (hmax := hmax) (handle := hh)) (.frame (D.cutShortSeam q w.shape true) true))).reindex
      (D.cutMirrorSeamColumns q w) (D.cutMirrorSeamRows q w)).linearEquiv=w.mirrorLastFrame T

lemma mirrorLast_frameCoordinates :
    D.MirrorLastFrameCoordinates q g J w T hproper hmax := by
  intro hh
  have hcanonical := valuesFromPorts_frameCoordinates_canonical (C) (FF)
    (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks (fun a => g (.side a)) J (Y))
    hh (D.cutShortSeam q w.shape true) true
    (D.cutMirrorSeamColumns q w) (D.cutMirrorSeamRows q w)
  have hcoordinates := (C0).frameValues_coordinates (FF0)
    ⟨.inr (.inr (Fin.last w.shape.atomicBand.length)),(w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).mirrorPort (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output⟩
    (D.cutShortSeam q w.shape true) true (D.cutMirrorLastOutput_attach q w)
    (D.cutMirrorActualColumns q w (Fin.last w.shape.atomicBand.length) (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output w.lastColumns.symm)
    (D.cutMirrorActualRows q w (Fin.last w.shape.atomicBand.length) (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output w.lastParent_rank)
    (D.cutMirrorSeamColumns q w) (D.cutMirrorSeamRows q w)
    (D.cutMirrorSeamColumns_coordinates q w (Fin.last w.shape.atomicBand.length) (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output w.lastColumns.symm true
      (D.cutMirrorLastOutput_attach q w)
      (by
        intro i
        change ((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).childEnumeration (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output (w.lastChild.symm i.1)).val=i.1.val
        simp only [IdentifiedBand.lastChild,Equiv.symm_trans_apply,Equiv.apply_symm_apply]
        rfl)
      (sigmaFinCongr_symm_val (m := D.childDim q) w.lastChild w.lastChild_rank))
    (D.cutMirrorSeamRows_coordinates q w (Fin.last w.shape.atomicBand.length) (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output w.lastParent_rank true
      (D.cutMirrorLastOutput_attach q w))
  have hframe := D.cutMirror_frameCoordinates q w (Fin.last w.shape.atomicBand.length) (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output w.lastColumns.symm w.lastParent_rank
      (D.portFrame g) T
  unfold CutMirrorFrameCoordinates at hframe
  exact hcanonical.trans (hcoordinates.trans hframe)

/-- The mirror parent word has the coordinates of the conjugated cut transport. -/
def MirrorParentCoordinates : Prop :=
  ∀ hh : (C).HandleValues (R:=K),
    ((MatrixIso.unit (((C).parentWord (D.cutShortSeam q w.shape true)).eval φ (mirrorShortGeneratorValues (D := D) (q := q) (g := g) (J := J) (w := w) (T := T) (hproper := hproper) (hmax := hmax) (handle := hh)))).reindex
      (D.cutMirrorSeamRows q w) (D.cutMirrorSeamRows q w)).linearEquiv=
        cutInnerLinear (D.namedParentLinear q g) (MatrixIso.unit J).linearEquiv T

lemma mirrorParent_coordinates :
    D.MirrorParentCoordinates q g J w T hproper hmax φ := by
  intro hh
  have hp := mirrorParentWord_coordinates (C) (D.cutShortSeam q w.shape true) φ (FF)
      (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks (fun a => g (.side a)) J (Y)) hh
      (D.cutShortSideRank q w.shape rfl w.rowRanks w.colRanks true none) (Y)
      (D.refinedCutSideValues_mirror_parent q w.shape rfl w.rowRanks w.colRanks
        (fun a=>g (.side a)) J (Y))
      (D.cutMirrorSeamRows q w) rfl
  exact hp.trans (MatrixIso.cutInnerUnit_linear (g (.side ⟨q,none⟩)) J T)

/-- The inverse child word of the mirror short seam acts as the identity. -/
def MirrorChildCoordinates : Prop :=
  ∀ hh : (C).HandleValues (R:=K),
    ((MatrixIso.unit ((Term.block ((C).childDim (D.cutShortSeam q w.shape true))
      (fun j => Term.inv ((C).childWord (D.cutShortSeam q w.shape true) j))).eval φ (mirrorShortGeneratorValues (D := D) (q := q) (g := g) (J := J) (w := w) (T := T) (hproper := hproper) (hmax := hmax) (handle := hh)))).reindex
      (D.cutMirrorSeamColumns q w) (D.cutMirrorSeamColumns q w)).linearEquiv=
        LinearEquiv.refl K (((i : Fin (arity q)) × Fin (D.childDim q i)) → K)

lemma mirrorChild_coordinates :
    D.MirrorChildCoordinates q g J w T hproper hmax φ := by
  intro hh
  have hc := (C).valuesFromPorts_childWord_coordinates (D.cutShortSeam q w.shape true) φ (FF)
      (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks (fun a => g (.side a)) J (Y)) hh
      (D.childDim q)
      (finCongr (D.cutShortSeam_arity q w.shape true).symm)
      (fun i=>(D.cutShortSideRank q w.shape rfl w.rowRanks w.colRanks true (some i)).symm)
      (fun _=>1)
      (fun i=>D.refinedCutSideValues_mirror_child q w.shape rfl w.rowRanks w.colRanks
        (fun a=>g (.side a)) J (Y) i)
      (D.cutMirrorSeamColumns q w) rfl
  exact hc.trans (MatrixIso.blockUnitOne_linear (D.childDim q))

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
