import OAI.AlgebraicGeometry.CharacterVarieties.Frames.BandBases
import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.RefinedDiagram

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open MatrixExpression NamedBandGrades OccurrenceIncidence
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S)

/-- Connected-strip incidence constructed from a pair of seam frames. -/
def cutFromOldFrames [Finite V]
    (f h : (Matrix (Fin (D.seamDim q)) (Fin (D.seamDim q)) K)ˣ) :=
  D.refinedCutDiagram q (D.bandFromOldFrames q f h).shape rfl
    (D.bandFromOldFrames q f h).rowRanks (D.bandFromOldFrames q f h).colRanks
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.PortWiring
open scoped Classical
open VertexTable
variable {F V : Type} {kind : V → Kind} (W : PortWiring kind)
    (d : (v : V) → Decoration (kind v) F) (h : W.ColorMatch d)
lemma colored_local_color (x : LocalEnd V kind) :
    (W.colored d h).facet (((W.colored d h).realize x).1)=(d x.1).color x.2 := by
  change W.seamColor d (((W.assemble _ _).realize x).1)=_
  rw [W.realize_assemble]
  exact W.seamColor_sideOf d h x
end IntegralCharacterVarieties.OccurrenceIncidence.PortWiring
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
open scoped Classical
variable {R : Type} [CommRing R] {k : Kind} {d e : LocalRanks k}
def transportFrames (h : d=e)
    (f : (p : k.table.Port) → MatrixIso R (d.Columns p) (d.Parent p)) :
    (p : k.table.Port) → MatrixIso R (e.Columns p) (e.Parent p) := h ▸ f
lemma transportFrames_holds (h : d=e)
    (f : (p : k.table.Port) → MatrixIso R (d.Columns p) (d.Parent p))
    (hf : (comparison k d f).Holds) : (comparison k e (transportFrames h f)).Holds := by
  subst e
  exact hf
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.LocalRanks
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence VertexTable TwoFlagBand
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity) (q : S)
variable {r : ℕ} (d : RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
variable [Finite V]
local notation "C" => D.refinedCutDiagram q d hp hc hc'
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)
local notation "B" => D.ports.refinedBandForSeam q d
lemma refinedCut_vertex_rank (v) (p) (c) :
    ((C).vertexRanks v).rank p c=D.ports.refinedRank q d D.rank
      ((BandGraft.decoration A q B v).color ⟨p,c⟩) := by
  apply congrArg (D.ports.refinedRank q d D.rank)
    ((BandGraft.wiring A q B).colored_local_color (BandGraft.decoration A q B)
      (BandGraft.colorMatch A q B) ⟨v,p,c⟩)
lemma refinedCut_old_vertexRanks (v : V) : (C).vertexRanks (.inl v)=D.vertexRanks v := by
  apply LocalRanks.ext_rank
  funext p c
  rw [D.refinedCut_vertex_rank q d hp hc hc']
  rfl
lemma refinedCut_orig_ranks (v : Fin (d.atomicBand.length+1)) (p) (c) :
    (d.vertexAtoms v).rank ⟨p,c⟩=((C).vertexRanks (.inr (.inl v))).rank p c := by
  exact ((d.vertexAtoms_rank v ⟨p,c⟩).trans
    (D.ports.refinedBandForSeam_rank q d D.rank hp hc hc' v ⟨p,c⟩).symm).trans
      (D.refinedCut_vertex_rank q d hp hc hc' (.inr (.inl v)) p c).symm
lemma refinedCut_mirror_ranks (v : Fin (d.atomicBand.length+1)) (p) (c) :
    (d.vertexAtoms v).mirror.rank ⟨p,c⟩=((C).vertexRanks (.inr (.inr v))).rank p c := by
  let z := (d.atomicBand.kind v).mirrorEnd.symm ⟨p,c⟩
  exact ((d.vertexAtoms_rank v z).trans
    (D.ports.refinedBandForSeam_rank q d D.rank hp hc hc' v z).symm).trans
      (D.refinedCut_vertex_rank q d hp hc hc' (.inr (.inr v)) p c).symm

variable {R : Type} [CommRing R]
def refinedOldFrames (f : D.PortFrames (R:=R)) (v : V) :
    (p : D.ports.kind v |>.table.Port) →
      @MatrixIso R _ (((C).vertexRanks (.inl v)).Columns p) (((C).vertexRanks (.inl v)).Parent p)
        (((C).vertexRanks (.inl v)).fintypeColumns p) inferInstance :=
  LocalRanks.transportFrames (D.refinedCut_old_vertexRanks q d hp hc hc' v).symm
    (fun p => f ⟨v,p⟩)

def refinedOrigFrames (v : Fin (d.atomicBand.length+1)) :
    (p : (d.atomicBand.kind v).table.Port) →
      @MatrixIso R _ (((C).vertexRanks (.inr (.inl v))).Columns p)
        (((C).vertexRanks (.inr (.inl v))).Parent p)
        (((C).vertexRanks (.inr (.inl v))).fintypeColumns p) inferInstance :=
  (d.vertexAtoms v).framesAtRanks _ (D.refinedCut_orig_ranks q d hp hc hc' v)

def refinedMirrorFrames (v : Fin (d.atomicBand.length+1)) :
    (p : (d.atomicBand.kind v).mirror.table.Port) →
      @MatrixIso R _ (((C).vertexRanks (.inr (.inr v))).Columns p)
        (((C).vertexRanks (.inr (.inr v))).Parent p)
        (((C).vertexRanks (.inr (.inr v))).fintypeColumns p) inferInstance :=
  (d.vertexAtoms v).mirror.framesAtRanks _ (D.refinedCut_mirror_ranks q d hp hc hc' v)

/-- The original and atomic frames satisfy the local vertex equations before the global gauge
changes. -/
def refinedCutVertexFrames (f : D.PortFrames (R:=R)) (v : V ⊕ (Fin (d.atomicBand.length+1) ⊕ Fin (d.atomicBand.length+1))) :
    (p : ((C).ports.kind v).table.Port) →
      MatrixIso R (((C).vertexRanks v).Columns p) (((C).vertexRanks v).Parent p) := by
  rcases v with v|v|v
  · exact D.refinedOldFrames q d hp hc hc' f v
  · exact D.refinedOrigFrames q d hp hc hc' v
  · exact D.refinedMirrorFrames q d hp hc hc' v

def refinedCutPortFrames (f : D.PortFrames (R:=R)) : (C).PortFrames (R:=R) :=
  fun p => D.refinedCutVertexFrames q d hp hc hc' f p.1 p.2

lemma refinedCutPortFrames_holds (f : D.PortFrames (R:=R))
    (hf : ∀ v,(LocalRanks.comparison (D.ports.kind v) (D.vertexRanks v) (fun p => f ⟨v,p⟩)).Holds)
    (v) : (LocalRanks.comparison ((C).ports.kind v) ((C).vertexRanks v)
      (fun p => D.refinedCutPortFrames q d hp hc hc' f ⟨v,p⟩)).Holds := by
  rcases v with v|v|v
  · change (LocalRanks.comparison _ _ (D.refinedOldFrames q d hp hc hc' f v)).Holds
    exact LocalRanks.transportFrames_holds _ _ (hf v)
  · exact (d.vertexAtoms v).framesAtRanks_holds _ (D.refinedCut_orig_ranks q d hp hc hc' v)
  · exact (d.vertexAtoms v).mirror.framesAtRanks_holds _ (D.refinedCut_mirror_ranks q d hp hc hc' v)
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
