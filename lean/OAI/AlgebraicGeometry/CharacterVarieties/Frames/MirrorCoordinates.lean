import OAI.AlgebraicGeometry.CharacterVarieties.Frames.Mirror
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.LocalFrames
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.FramedFlags

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades
private lemma transportFrames_coordinateComposition
    {K I J A B : Type} [CommRing K] [Fintype I] [Fintype J] [Fintype A] [Fintype B]
    {k : Kind} {d d' : LocalRanks k} (hd : d = d')
    (f : (p : k.table.Port) → MatrixIso K (d.Columns p) (d.Parent p))
    (p : k.table.Port) (s : A ≃ d.Columns p) (t : B ≃ d.Parent p)
    (e : I ≃ A) (r : J ≃ B) :
    ((LocalRanks.transportFrames hd f p).reindex
      (e.trans (s.trans (LocalRanks.columnCongr hd p)))
      (r.trans (t.trans (LocalRanks.parentCongr hd p)))).linearEquiv =
      (((f p).reindex s t).reindex e r).linearEquiv := by
  have hh := congrArg (fun z : MatrixIso K (d.Columns p) (d.Parent p) =>
      ((z.reindex s t).reindex e r).linearEquiv)
    (LocalRanks.transportFrames_reindex hd f p)
  simpa only [MatrixIso.reindex_reindex_eq, Equiv.trans_assoc] using hh

variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
variable (v : Fin (w.shape.atomicBand.length+1)) (p : (w.shape.atomicBand.kind v).table.Port)

variable {I : Type} (e : I ≃ (w.shape.vertexAtoms v).localRanks.Columns p)
    (hr : (w.shape.vertexAtoms v).rank ⟨p,none⟩=D.rank (D.ports.facet ⟨q,none⟩))

def cutMirrorActualColumns : I ≃ ((C).vertexRanks (.inr (.inr v))).Columns ((w.shape.atomicBand.kind v).mirrorPort p) :=
  e.trans (((w.shape.vertexAtoms v).seamColumns (w.shape.vertexAtoms v).mirror p ((w.shape.atomicBand.kind v).mirrorPort p) ((w.shape.atomicBand.kind v).mirrorChild p) (fun c => ((w.shape.vertexAtoms v).mirror_atoms ⟨p,some c⟩).symm)).trans
    (LocalRanks.columnCongr (D.namedCut_mirror_localRanks q w v) ((w.shape.atomicBand.kind v).mirrorPort p)))
def cutMirrorActualRows : Fin (D.rank (D.ports.facet ⟨q,none⟩)) ≃
    ((C).vertexRanks (.inr (.inr v))).Parent ((w.shape.atomicBand.kind v).mirrorPort p) :=
  (finCongr hr).symm.trans ((finCongr ((w.shape.vertexAtoms v).rank_of_atoms (w.shape.vertexAtoms v).mirror (((w.shape.vertexAtoms v).mirror_atoms ⟨p,none⟩).symm))).trans
    (LocalRanks.parentCongr (D.namedCut_mirror_localRanks q w v) ((w.shape.atomicBand.kind v).mirrorPort p)))

/-- Equality of the transported and aligned mirror frames in the original port coordinates. -/
def CutMirrorFrameCoordinates [Fintype I] (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) : Prop :=
    (((D.namedCutPortFrames q w old T) ⟨.inr (.inr v),((w.shape.atomicBand.kind v).mirrorPort p)⟩).reindex
      (D.cutMirrorActualColumns q w v p e) (D.cutMirrorActualRows q w v p hr)).linearEquiv=
    ((w.mirrorAlignedFrame T v p).reindex e (finCongr hr).symm).linearEquiv

lemma cutMirror_frameCoordinates [Fintype I] (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) :
    D.CutMirrorFrameCoordinates q w v p e hr old T := by
  unfold CutMirrorFrameCoordinates
  exact transportFrames_coordinateComposition
    (D.namedCut_mirror_localRanks q w v) (w.mirrorVertexFrames T v)
    ((w.shape.atomicBand.kind v).mirrorPort p)
    ((w.shape.vertexAtoms v).seamColumns (w.shape.vertexAtoms v).mirror p
      ((w.shape.atomicBand.kind v).mirrorPort p) ((w.shape.atomicBand.kind v).mirrorChild p)
      (fun c => ((w.shape.vertexAtoms v).mirror_atoms ⟨p,some c⟩).symm))
    (finCongr ((w.shape.vertexAtoms v).rank_of_atoms (w.shape.vertexAtoms v).mirror
      (((w.shape.vertexAtoms v).mirror_atoms ⟨p,none⟩).symm)))
    e (finCongr hr).symm

/-- The child label and the coordinate within that child at a mirror port. -/
def cutMirrorColumnCoordinates (i : I) : ℕ × ℕ :=
  ((((C).ports.kind (.inr (.inr v))).childEnumeration
      ((w.shape.atomicBand.kind v).mirrorPort p)
      (D.cutMirrorActualColumns q w v p e i).1).val,
    (D.cutMirrorActualColumns q w v p e i).2.val)

lemma cutMirrorActualColumns_childEnumeration (i : I) :
    (D.cutMirrorColumnCoordinates q w v p e i).1 =
      ((w.shape.atomicBand.kind v).childEnumeration p (e i).1).val := by
  change ((w.shape.atomicBand.kind v).mirror.childEnumeration ((w.shape.atomicBand.kind v).mirrorPort p) ((w.shape.atomicBand.kind v).mirrorChild p (e i).1)).val=_
  rw [Kind.mirror_childEnumeration]
  rfl

lemma cutMirrorActualColumns_value (i : I) :
    (D.cutMirrorColumnCoordinates q w v p e i).2 = (e i).2.val := by
  rfl

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable TwoFlagBand NamedBandGrades MatrixExpression
variable {F S V : Type} {arity : S → ℕ}
    (D : Diagram F S V arity) (q : S)
    {r : ℕ} (d : RankShape (arity q) (arity q) r)
local notation "B" => D.ports.refinedBandForSeam q d
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)
private lemma shortSignatureMatch :
    (B).doublePatch.SignatureMatch (doubleDecoration (B).decoration) :=
  (B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast
local notation "hi" => shortSignatureMatch D q d
private lemma shortPlusSignature :
    ∀ i, portSignature (doubleDecoration (B).decoration) ((B).doublePatch.plus (.inr i)).val =
      (A).seamSignature q := by
  intro i
  rw [(B).double_signature_plus]
  cases i <;> rfl

private lemma shortMinusSignature :
    ∀ i, portSignature (doubleDecoration (B).decoration) ((B).doublePatch.minus (.inr i)).val =
      (A).seamSignature q := by
  intro i
  rw [(B).double_signature_minus]
  cases i <;> rfl

local notation "hp'" => shortPlusSignature D q d
local notation "hm'" => shortMinusSignature D q d

def cutShortSeam (b : Bool) := graftPlus (A) (B).doublePatch (.inr (.inr b))
lemma cutShortSeam_arity (b : Bool) :
    (BandGraft.wiring (A) q (B)).seamArity (D.cutShortSeam q d b)=arity q :=
  graftLabelArity_short (A) (B).doublePatch (doubleDecoration (B).decoration) q (hi) (hp') (hm') b

variable [Finite V]
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
local notation "C" => D.refinedCutDiagram q d hp hc hc'

lemma cutShortSideRank (b : Bool) (i : Option (Fin (arity q))) :
    (C).rank ((C).ports.facet ⟨D.cutShortSeam q d b,
      i.map (finCongr (D.cutShortSeam_arity q d b).symm)⟩)=D.rank (D.ports.facet ⟨q,i⟩) := by
  exact congrArg (D.ports.refinedRank q d D.rank)
    (graft_short_color (A) (B).doublePatch (doubleDecoration (B).decoration) q (hi) (hp') (hm') b i)

variable {R : Type} [CommRing R]
variable (old : D.SideValues (R:=R))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) R)ˣ)
/-- The side value of a short seam, in the coordinate labels of the original seam. -/
def shortSeamSideValues (b : Bool) (i : Option (Fin (arity q))) :
    (Matrix (Fin (D.rank (D.ports.facet ⟨q,i⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,i⟩))) R)ˣ :=
  rebaseUnit (D.cutShortSideRank q d hp hc hc' b i)
    (D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨D.cutShortSeam q d b,i.map (finCongr (D.cutShortSeam_arity q d b).symm)⟩)

lemma refinedCutSideValues_short (b : Bool) (i : Option (Fin (arity q))) :
    D.shortSeamSideValues q d hp hc hc' old J Y b i =
      D.cutShortSideValues q Y b i := by
  exact graftSideValues_short (A) (B).doublePatch (doubleDecoration (B).decoration) q
    (hi) (hp') (hm') (D.ports.refinedRank q d D.rank)
    (D.cutOldSideValues q old J) (D.cutShortSideValues q Y) b i

lemma refinedCutSideValues_mirror_parent :
    D.shortSeamSideValues q d hp hc hc' old J Y true none = Y :=
  D.refinedCutSideValues_short q d hp hc hc' old J Y true none

lemma refinedCutSideValues_mirror_child (i : Fin (arity q)) :
    D.shortSeamSideValues q d hp hc hc' old J Y true (some i) = 1 :=
  D.refinedCutSideValues_short q d hp hc hc' old J Y true (some i)

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity)
    {I : Type} (p : LocalPort V D.ports.kind) (s : S) (b : Bool)
    (hp : D.ports.attach p=(s,b))
def columnsAt (e : I ≃ (D.vertexRanks p.1).Columns p.2) : I ≃ Fin (D.seamDim s) :=
  (e.trans (D.portColumnIndex p)).trans (finCongr (congrArg D.seamDim (congrArg Prod.fst hp)))
def rowsAt (e : I ≃ (D.vertexRanks p.1).Parent p.2) : I ≃ Fin (D.seamDim s) :=
  (e.trans (D.portRowIndex p)).trans (finCongr (congrArg D.seamDim (congrArg Prod.fst hp)))
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
