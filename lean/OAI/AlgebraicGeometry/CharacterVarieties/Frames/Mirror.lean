import OAI.AlgebraicGeometry.CharacterVarieties.Frames.Endpoints
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.CutFrames
import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.GraftValues

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
open scoped Classical
open TwoFlagBand OccurrenceIncidence VertexTable
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)

lemma mirrorColor_eq (T : MatrixIso K (Fin r) (Fin r))
    (c : Option (Secondary n n)) (hc : c≠none) : w.mirrorColorGauge T c=w.colorGauge c := by
  cases c with
  | none => exact (hc rfl).elim
  | some c => rfl

lemma child_color_ne (v : Fin (w.shape.atomicBand.length+1))
    (p : (w.shape.atomicBand.kind v).table.Port) (a : (w.shape.atomicBand.kind v).table.Child p) :
    (w.shape.atomicBand.decoration v).color ⟨p,some a⟩≠none := by
  obtain ⟨d,hd⟩ := w.shape.atomicBand_fresh v
  intro hh
  have he : ((w.shape.atomicBand.kind v).freshDecoration d).color ⟨p,some a⟩=none := hd ▸ hh
  rcases ((w.shape.atomicBand.kind v).fresh_color_none d _).mp he with hh|hh <;> cases hh

lemma mirror_basis (T : MatrixIso K (Fin r) (Fin r))
    (v : Fin (w.shape.atomicBand.length+1)) (z)
    (hz : (w.shape.atomicBand.decoration v).color z≠none) :
    ((w.mirrorVertexBases T v).basis ((w.shape.atomicBand.kind v).mirrorEnd z).1
      ((w.shape.atomicBand.kind v).mirrorEnd z).2).reindex
        (finCongr ((w.shape.vertexAtoms v).mirror.rank_of_atoms (w.shape.vertexAtoms v)
          ((w.shape.vertexAtoms v).mirror_atoms z))).symm
        (finCongr ((w.shape.vertexAtoms v).mirror.rank_of_atoms (w.shape.vertexAtoms v)
          ((w.shape.vertexAtoms v).mirror_atoms z))).symm =
      (w.vertexBases v).basis z.1 z.2 := by
  let e := (w.shape.atomicBand.kind v).mirrorEnd
  let c := (w.shape.atomicBand.decoration v).color z
  let c' := (w.shape.atomicBand.decoration v).color (e.symm (e z))
  have he : c'=c := congrArg (w.shape.atomicBand.decoration v).color (e.symm_apply_apply z)
  have hn : c'≠none := fun h => hz (he.symm.trans h)
  have hm := w.mirrorColor_eq T c' hn
  have hr := (w.shape.vertexAtoms v).mirror.rank_of_atoms (w.shape.vertexAtoms v)
    ((w.shape.vertexAtoms v).mirror_atoms z)
  have hh := MatrixIso.finite_basis_transport (freshRank r w.shape.secondaryRank) w.colorGauge
    c c' ((w.shape.vertexAtoms v).rank z) ((w.shape.vertexAtoms v).mirror.rank (e z))
    (w.shape.vertexAtoms_rank v z) (w.shape.vertexAtoms_rank v (e.symm (e z))) he.symm hr.symm
  exact (congrArg (fun g => (g.reindex
    (finCongr (w.shape.vertexAtoms_rank v (e.symm (e z))))
    (finCongr (w.shape.vertexAtoms_rank v (e.symm (e z))))).reindex
    (finCongr hr.symm) (finCongr hr.symm)) hm).trans hh

lemma transverse_parent_color (v : Fin (w.shape.atomicBand.length+1))
    (p : (w.shape.atomicBand.kind v).table.Port)
    (hin : p≠(w.shape.atomicBand.kind v).input) (hout : p≠(w.shape.atomicBand.kind v).output) :
    (w.shape.atomicBand.decoration v).color ⟨p,none⟩≠none := by
  obtain ⟨d,hd⟩ := w.shape.atomicBand_fresh v
  intro hh
  have he : ((w.shape.atomicBand.kind v).freshDecoration d).color ⟨p,none⟩=none := hd ▸ hh
  rcases ((w.shape.atomicBand.kind v).fresh_color_none d _).mp he with hh|hh
  · exact hin (congrArg Sigma.fst hh)
  · exact hout (congrArg Sigma.fst hh)

/-- The transverse branch has smaller parent rank, so its parent and child transports are identities
under the mirror principal gauge. -/
lemma transverse_frame_seam (T : MatrixIso K (Fin r) (Fin r))
    (v : Fin (w.shape.atomicBand.length+1)) (p : (w.shape.atomicBand.kind v).table.Port)
    (hin : p≠(w.shape.atomicBand.kind v).input) (hout : p≠(w.shape.atomicBand.kind v).output) :
    (w.mirrorVertexFrames T v ((w.shape.atomicBand.kind v).mirrorPort p)).reindex
      ((w.shape.vertexAtoms v).seamColumns (w.shape.vertexAtoms v).mirror
        p ((w.shape.atomicBand.kind v).mirrorPort p) ((w.shape.atomicBand.kind v).mirrorChild p)
        (fun a => ((w.shape.vertexAtoms v).mirror_atoms ⟨p,some a⟩).symm))
      (finCongr ((w.shape.vertexAtoms v).rank_of_atoms (w.shape.vertexAtoms v).mirror
        ((w.shape.vertexAtoms v).mirror_atoms ⟨p,none⟩).symm))=w.vertexFrames v p := by
  apply (w.shape.vertexAtoms v).reframe_seam (w.shape.vertexAtoms v).mirror
    (w.vertexBases v) (w.mirrorVertexBases T v) p ((w.shape.atomicBand.kind v).mirrorPort p)
    ((w.shape.atomicBand.kind v).mirrorChild p)
    ((w.shape.vertexAtoms v).mirror_atoms ⟨p,none⟩).symm
    (fun a => ((w.shape.vertexAtoms v).mirror_atoms ⟨p,some a⟩).symm)
  · exact w.mirror_basis T v ⟨p,none⟩ (w.transverse_parent_color v p hin hout)
  · intro a
    exact w.mirror_basis T v ⟨p,some a⟩ (w.child_color_ne v p a)

end IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence VertexTable TwoFlagBand NamedBandGrades
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
lemma namedCut_orig_localRanks (v : Fin (w.shape.atomicBand.length+1)) :
    (w.shape.vertexAtoms v).localRanks=(C).vertexRanks (.inr (.inl v)) := by
  apply LocalRanks.ext_rank
  funext p c
  exact D.refinedCut_orig_ranks q w.shape rfl w.rowRanks w.colRanks v p c
lemma namedCut_mirror_localRanks (v : Fin (w.shape.atomicBand.length+1)) :
    (w.shape.vertexAtoms v).mirror.localRanks=(C).vertexRanks (.inr (.inr v)) := by
  apply LocalRanks.ext_rank
  funext p c
  exact D.refinedCut_mirror_ranks q w.shape rfl w.rowRanks w.colRanks v p c

def namedCutOrigFrames (v : Fin (w.shape.atomicBand.length+1)) :=
  LocalRanks.transportFrames (D.namedCut_orig_localRanks q w v) (w.vertexFrames v)
def namedCutMirrorFrames (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
    (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) (v : Fin (w.shape.atomicBand.length+1)) :=
  LocalRanks.transportFrames (D.namedCut_mirror_localRanks q w v) (w.mirrorVertexFrames T v)

def namedCutVertexFrames (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (v : V ⊕ (Fin (w.shape.atomicBand.length+1) ⊕ Fin (w.shape.atomicBand.length+1))) :
    (p : ((C).ports.kind v).table.Port) →
      MatrixIso K (((C).vertexRanks v).Columns p) (((C).vertexRanks v).Parent p) := by
  rcases v with v|v|v
  · exact D.refinedOldFrames q w.shape rfl w.rowRanks w.colRanks old v
  · exact D.namedCutOrigFrames q w v
  · exact D.namedCutMirrorFrames q w T v

def namedCutPortFrames (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))) : (C).PortFrames (R:=K) :=
  fun p => D.namedCutVertexFrames q w old T p.1 p.2

lemma namedCutPortFrames_holds (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (hold : ∀ v,(LocalRanks.comparison (D.ports.kind v) (D.vertexRanks v)
      (fun p => old ⟨v,p⟩)).Holds)
    (v) : (LocalRanks.comparison ((C).ports.kind v) ((C).vertexRanks v)
      (fun p => D.namedCutPortFrames q w old T ⟨v,p⟩)).Holds := by
  rcases v with v|v|v
  · exact LocalRanks.transportFrames_holds _ _ (hold v)
  · exact LocalRanks.transportFrames_holds _ _ (w.vertexFrames_holds v)
  · exact LocalRanks.transportFrames_holds _ _ (w.mirrorVertexFrames_holds T v)
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable TwoFlagBand NamedBandGrades
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (D : Diagram F S V arity) (q : S)
    {r : ℕ} (d : RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
local notation "B" => D.ports.refinedBandForSeam q d
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)

/-- The selected original parent side changes from P to J; children retain their transports over the
coefficient ring. -/
def cutOldSideValues (old : D.SideValues (R:=R)) (J : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩))) (Fin (D.rank (D.ports.facet ⟨q,none⟩))) R)ˣ) : D.SideValues (R:=R)
  | ⟨s,none⟩ => if h : s=q then h.symm ▸ J else old ⟨s,none⟩
  | ⟨s,some i⟩ => old ⟨s,some i⟩

lemma cutOldSideValues_selected (old : D.SideValues (R:=R)) (J : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩))) (Fin (D.rank (D.ports.facet ⟨q,none⟩))) R)ˣ) :
    D.cutOldSideValues q old J ⟨q,none⟩=J := by simp only [cutOldSideValues,dite_true]
lemma cutOldSideValues_child (old : D.SideValues (R:=R)) (J : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩))) (Fin (D.rank (D.ports.facet ⟨q,none⟩))) R)ˣ) (s) (i) :
    D.cutOldSideValues q old J ⟨s,some i⟩=old ⟨s,some i⟩ := rfl

/-- New strip sides have identity transport except for the mirror principal short seam, which
carries Y = T⁻¹ J⁻¹ P T. -/
def cutShortSideValues (Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩))) (Fin (D.rank (D.ports.facet ⟨q,none⟩))) R)ˣ) (b : Bool) (i : Option (Fin (arity q))) :
    FacetUnit (R:=R) D.rank (D.ports.facet ⟨q,i⟩) := by
  cases i with
  | none => exact if b then Y else 1
  | some _ => exact 1

lemma refinedGenus_inl_le (f : F) : D.refinedGenus q d (.inl f)≤D.genus f := by
  change (if f=D.ports.facet ⟨q,none⟩ then D.genus f-1 else D.genus f)≤D.genus f
  split_ifs <;> omega

variable [Finite V]
local notation "C" => D.refinedCutDiagram q d hp hc hc'

def refinedCutSideValues (old : D.SideValues (R:=R)) (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩))) (Fin (D.rank (D.ports.facet ⟨q,none⟩))) R)ˣ) : (C).SideValues (R:=R) :=
  graftSideValues (A) (B).doublePatch (doubleDecoration (B).decoration) q
    ((B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast)
    (fun i => by rw [(B).double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [(B).double_signature_minus]; cases i <;> rfl)
    (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J) (D.cutShortSideValues q Y)

/-- The original handles are retained except for the last handle of the selected parent. New strip
facets are disks. -/
def refinedCutHandleValues (old : D.HandleValues (R:=R)) : (C).HandleValues (R:=R) := by
  intro f i b
  cases f with
  | inl f => exact old f ⟨i.val,i.isLt.trans_le (D.refinedGenus_inl_le q d f)⟩ b
  | inr f => exact Fin.elim0 i
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
