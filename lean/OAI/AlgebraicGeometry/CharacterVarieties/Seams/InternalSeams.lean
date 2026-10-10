import OAI.AlgebraicGeometry.CharacterVarieties.Frames.MarkedFrames
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.FrameTransport
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.PortCoordinates
import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.BandCut

namespace OAI

/-!
# Internal seam equations

Compatibility of the frames on adjacent original, reflected, and transverse
branches of an identified band.
-/

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
/-- The child identifications across every original internal seam. -/
def OriginalChildrenMatch : Prop :=
  ∀ (j : Fin w.shape.atomicBand.length),
    (C).portChildMatch ⟨.inr (.inl j.castSucc),(w.shape.atomicBand.kind j.castSucc).output⟩
      ⟨.inr (.inl j.succ),(w.shape.atomicBand.kind j.succ).input⟩
      (D.origAdjacentSame q w j)=w.interiorChild j
lemma origChildMatch : D.OriginalChildrenMatch q w := by
  intro j
  change
    (C).portChildMatch ⟨.inr (.inl j.castSucc),(w.shape.atomicBand.kind j.castSucc).output⟩
      ⟨.inr (.inl j.succ),(w.shape.atomicBand.kind j.succ).input⟩
      (D.origAdjacentSame q w j)=w.interiorChild j
  apply (C).portChildMatch_eq_of_enumeration
  intro c
  change (w.shape.atomicBand.kind j.castSucc).table.Child (w.shape.atomicBand.kind j.castSucc).output at c
  change (((w.shape.atomicBand.kind j.succ).childEnumeration (w.shape.atomicBand.kind j.succ).input) (w.interiorChild j c)).val=
    (((w.shape.atomicBand.kind j.castSucc).childEnumeration (w.shape.atomicBand.kind j.castSucc).output) c).val
  unfold IdentifiedBand.interiorChild
  simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
  rfl
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
    (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "FF" => D.namedCutPortFrames q w old T
/-- Compatibility of the transported frames across an original internal seam. -/
def OriginalFrameMatch (j : Fin w.shape.atomicBand.length) : Prop :=
    ((FF) ⟨.inr (.inl j.succ),(w.shape.atomicBand.kind j.succ).input⟩).reindex
      ((C).portColumnMatch ⟨.inr (.inl j.castSucc),(w.shape.atomicBand.kind j.castSucc).output⟩
        ⟨.inr (.inl j.succ),(w.shape.atomicBand.kind j.succ).input⟩ (D.origAdjacentSame q w j))
      ((C).portParentMatch ⟨.inr (.inl j.castSucc),(w.shape.atomicBand.kind j.castSucc).output⟩
        ⟨.inr (.inl j.succ),(w.shape.atomicBand.kind j.succ).input⟩ (D.origAdjacentSame q w j))=
      (FF) ⟨.inr (.inl j.castSucc),(w.shape.atomicBand.kind j.castSucc).output⟩
lemma origFrameMatch (j : Fin w.shape.atomicBand.length) : D.OriginalFrameMatch q w old T j := by
  change
    ((FF) ⟨.inr (.inl j.succ),(w.shape.atomicBand.kind j.succ).input⟩).reindex
      ((C).portColumnMatch ⟨.inr (.inl j.castSucc),(w.shape.atomicBand.kind j.castSucc).output⟩
        ⟨.inr (.inl j.succ),(w.shape.atomicBand.kind j.succ).input⟩ (D.origAdjacentSame q w j))
      ((C).portParentMatch ⟨.inr (.inl j.castSucc),(w.shape.atomicBand.kind j.castSucc).output⟩
        ⟨.inr (.inl j.succ),(w.shape.atomicBand.kind j.succ).input⟩ (D.origAdjacentSame q w j))=
      (FF) ⟨.inr (.inl j.castSucc),(w.shape.atomicBand.kind j.castSucc).output⟩
  exact (C).transported_portFrame_match _ _ (D.origAdjacentSame q w j)
    (D.namedCut_orig_localRanks q w j.castSucc) (D.namedCut_orig_localRanks q w j.succ)
    (w.vertexFrames j.castSucc) (w.vertexFrames j.succ) (w.interiorChild j)
    (D.origChildMatch q w j).symm
    (fun a => (w.shape.vertexAtoms j.castSucc).rank_of_atoms (w.shape.vertexAtoms j.succ)
      (congrArg w.shape.facetAtoms (w.interior_child j a)))
    ((w.shape.vertexAtoms j.castSucc).rank_of_atoms (w.shape.vertexAtoms j.succ)
      (congrArg w.shape.facetAtoms (w.interior_parent j)))
    (w.interior_frame_seam j)
/-- Equality of the two frame values on an original internal seam. -/
def OriginalFrameValuesAgree (j : Fin w.shape.atomicBand.length) : Prop :=
    (C).frameValues (FF)
      (BandGraft.originalPort
        (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
        (D.ports.refinedBandForSeam q w.shape) j.succ true) false=
    (C).frameValues (FF)
      (BandGraft.originalPort
        (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
        (D.ports.refinedBandForSeam q w.shape) j.succ true) true
lemma origFrameValues_eq (j : Fin w.shape.atomicBand.length) : D.OriginalFrameValuesAgree q w old T j := by
  change
    (C).frameValues (FF)
      (BandGraft.originalPort
        (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
        (D.ports.refinedBandForSeam q w.shape) j.succ true) false=
    (C).frameValues (FF)
      (BandGraft.originalPort
        (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
        (D.ports.refinedBandForSeam q w.shape) j.succ true) true
  exact (C).frameValues_seam_of_ports (FF) _ _ _
    (D.origOutput_attach q w j) (D.origInput_attach q w j.succ)
    (D.origAdjacentSame q w j) (D.origFrameMatch q w old T j)
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical Matrix
open VertexTable SurfacePresentation.Diagram
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
variable (rank : F → ℕ)
    (old : (s : Side S arity) → FacetUnit (R:=R) rank (A.facet s))
    (short : Bool → (i : Option (Fin (arity q))) → FacetUnit (R:=R) rank (A.facet ⟨q,i⟩))
lemma bandValues_original_succ (j : Fin B.length)
    (i : Option (Fin ((wiring A q B).seamArity (originalPort A q B j.succ true)))) :
    bandValues A q B rank old short ⟨originalPort A q B j.succ true,i⟩=1 := by
  exact graftSideValues_internal A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl) rank old short
    (.inl (.inl j)) i
lemma bandValues_mirror_castSucc (j : Fin B.length)
    (i : Option (Fin ((wiring A q B).seamArity (mirrorOutput A q B j.castSucc)))) :
    bandValues A q B rank old short ⟨mirrorOutput A q B j.castSucc,i⟩=1 := by
  exact graftSideValues_internal A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl) rank old short
    (.inl (.inr j)) i
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable TwoFlagBand NamedBandGrades
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {r : ℕ} (d : RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
local notation "C" => D.refinedCutDiagram q d hp hc hc'
local notation "B" => D.ports.refinedBandForSeam q d
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)
variable (old : D.SideValues (R:=R))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩))) (Fin (D.rank (D.ports.facet ⟨q,none⟩))) R)ˣ)
/-- The side values on every original internal seam are trivial. -/
def OriginalInternalSideValuesTrivial : Prop :=
  ∀ (j : Fin d.atomicBand.length)
    (i : Option (Fin ((BandGraft.wiring (A) q (B)).seamArity (BandGraft.originalPort (A) q (B) j.succ true)))),
    D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨BandGraft.originalPort (A) q (B) j.succ true,i⟩=1
lemma refinedCutSideValues_original_succ : D.OriginalInternalSideValuesTrivial q d hp hc hc' old J Y := by
  intro j i
  change
    D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨BandGraft.originalPort (A) q (B) j.succ true,i⟩=1
  exact BandGraft.bandValues_original_succ (A) q (B)
    (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J) (D.cutShortSideValues q Y) j i
/-- The side values on every reflected internal seam are trivial. -/
def MirrorInternalSideValuesTrivial : Prop :=
  ∀ (j : Fin d.atomicBand.length)
    (i : Option (Fin ((BandGraft.wiring (A) q (B)).seamArity (BandGraft.mirrorOutput (A) q (B) j.castSucc)))),
    D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨BandGraft.mirrorOutput (A) q (B) j.castSucc,i⟩=1
lemma refinedCutSideValues_mirror_castSucc : D.MirrorInternalSideValuesTrivial q d hp hc hc' old J Y := by
  intro j i
  change
    D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨BandGraft.mirrorOutput (A) q (B) j.castSucc,i⟩=1
  exact BandGraft.bandValues_mirror_castSucc (A) q (B)
    (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J) (D.cutShortSideValues q Y) j i
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression HomTransport
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
    (D : Diagram F S V arity) (φ : R →+* A)
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
lemma trivialSides_seam_eq (s : S)
    (hp : g (.side ⟨s,none⟩)=1)
    (hc : ∀ i,g (.side ⟨s,some i⟩)=1)
    (hf : g (.frame s false)=g (.frame s true)) :
    (D.seamLeft s).eval φ g=(D.seamRight s).eval φ g := by
  have ha : (D.parentWord s).eval φ g=rebaseUnit (D.seamRank s) (g (.side ⟨s,none⟩)) :=
    Term.eval_cast_unit φ g (D.seamRank s) (D.sideWord ⟨s,none⟩)
  have ha' : (D.parentWord s).eval φ g=1 := by
    rw [ha]
    erw [hp,map_one]
    rfl
  have hc' (j : Fin (arity s)) : ((D.childWord s j).eval φ g)⁻¹=1 := by
    change (g (.side ⟨s,some j⟩))⁻¹=1
    rw [hc j,inv_one]
  have hb : blockUnit (D.childDim s) (fun j => ((D.childWord s j).eval φ g)⁻¹)=1 := by
    simp only [hc',blockUnit_one]
  simp only [seamLeft,seamRight,Term.eval,ha',hb,frameWord,Term.eval,hf]
  erw [one_mul,mul_one]
lemma trivialSides_seamHolds (s : S)
    (hp : g (.side ⟨s,none⟩)=1)
    (hc : ∀ i,g (.side ⟨s,some i⟩)=1)
    (hf : g (.frame s false)=g (.frame s true)) :
    SameFramedFlag (D.seamGrade s)
      (matrixUnitEquiv ((D.seamLeft s).eval φ g))
      (matrixUnitEquiv ((D.seamRight s).eval φ g)) := by
  rw [D.trivialSides_seam_eq φ g s hp hc hf]
  exact ⟨fun _ => rfl,fun _ _ _ => rfl⟩
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K R : Type} {arity : S → ℕ} [Field K] [CommRing R]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
    (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
variable (φ : R →+* K) (side : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (handle : (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks).HandleValues (R:=K))
local notation "gg" => valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
  (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handle
/-- The framed flag equations on every original internal seam. -/
def OriginalInternalFlagsHold : Prop :=
  ∀ (handles : (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks).HandleValues (R:=K))
    (j : Fin w.shape.atomicBand.length),
    SameFramedFlag ((C).seamGrade (BandGraft.originalPort (A) q (B) j.succ true))
      (matrixUnitEquiv (((C).seamLeft (BandGraft.originalPort (A) q (B) j.succ true)).eval φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles)))
      (matrixUnitEquiv (((C).seamRight (BandGraft.originalPort (A) q (B) j.succ true)).eval φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles)))
lemma originalInternal_seamHolds : D.OriginalInternalFlagsHold q w old T φ side J Y := by
  intro handles j
  change
    SameFramedFlag ((C).seamGrade (BandGraft.originalPort (A) q (B) j.succ true))
      (matrixUnitEquiv (((C).seamLeft (BandGraft.originalPort (A) q (B) j.succ true)).eval φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles)))
      (matrixUnitEquiv (((C).seamRight (BandGraft.originalPort (A) q (B) j.succ true)).eval φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles)))
  exact (C).trivialSides_seamHolds φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles) _
    (D.refinedCutSideValues_original_succ q w.shape rfl w.rowRanks w.colRanks side J Y j none)
    (fun i => D.refinedCutSideValues_original_succ q w.shape rfl w.rowRanks w.colRanks side J Y j (some i))
    (D.origFrameValues_eq q w old T j)
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
open scoped Classical
open TwoFlagBand OccurrenceIncidence VertexTable
variable {K : Type} [Field K] {n r : ℕ} {s : Fin n → ℕ}
    {f h : (((i : Fin n) × Fin (s i)) → K) ≃ₗ[K] (Fin r → K)}
    (w : IdentifiedBand s f h)
lemma interiorChild_enumeration (j : Fin w.shape.atomicBand.length)
    (c : (w.shape.atomicBand.kind j.castSucc).table.Child (w.shape.atomicBand.kind j.castSucc).output) :
    (((w.shape.atomicBand.kind j.succ).childEnumeration (w.shape.atomicBand.kind j.succ).input)
      (w.interiorChild j c)).val=
    (((w.shape.atomicBand.kind j.castSucc).childEnumeration (w.shape.atomicBand.kind j.castSucc).output) c).val := by
  simp only [interiorChild,Equiv.trans_apply,Equiv.apply_symm_apply]
  rfl
lemma mirrorInteriorChild_enumeration (j : Fin w.shape.atomicBand.length)
    (c : (w.shape.atomicBand.kind j.castSucc).mirror.table.Child
      ((w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output)) :
    (((w.shape.atomicBand.kind j.succ).mirror.childEnumeration
      ((w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input))
      (w.mirrorInteriorChild j c)).val=
    (((w.shape.atomicBand.kind j.castSucc).mirror.childEnumeration
      ((w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output)) c).val := by
  obtain ⟨c,rfl⟩ := ((w.shape.atomicBand.kind j.castSucc).mirrorChild _).surjective c
  simp only [mirrorInteriorChild,Equiv.trans_apply,Equiv.symm_apply_apply,
    Kind.mirror_childEnumeration]
  exact w.interiorChild_enumeration j c
end IntegralCharacterVarieties.NamedBandGrades.IdentifiedBand
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression NamedBandGrades VertexTable
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "W" => BandGraft.wiring (A) q (B)
/-- The attachment of each reflected output port. -/
def MirrorOutputAttached : Prop :=
  ∀ (v : Fin (w.shape.atomicBand.length+1)),
    (C).ports.attach ⟨.inr (.inr v),(w.shape.atomicBand.kind v).mirrorPort (w.shape.atomicBand.kind v).output⟩=
      (BandGraft.mirrorOutput (A) q (B) v,true)
lemma mirrorOutput_attach : D.MirrorOutputAttached q w := by
  intro v
  change
    (C).ports.attach ⟨.inr (.inr v),(w.shape.atomicBand.kind v).mirrorPort (w.shape.atomicBand.kind v).output⟩=
      (BandGraft.mirrorOutput (A) q (B) v,true)
  exact (W).endOf_portAt (BandGraft.mirrorOutput (A) q (B) v,true)
/-- The attachment of each reflected input port. -/
def MirrorInputAttached : Prop :=
  ∀ (j : Fin w.shape.atomicBand.length),
    (C).ports.attach ⟨.inr (.inr j.succ),(w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input⟩=
      (BandGraft.mirrorOutput (A) q (B) j.castSucc,false)
lemma mirrorInput_attach : D.MirrorInputAttached q w := by
  intro j
  change
    (C).ports.attach ⟨.inr (.inr j.succ),(w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input⟩=
      (BandGraft.mirrorOutput (A) q (B) j.castSucc,false)
  have hh := (W).endOf_portAt (BandGraft.mirrorOutput (A) q (B) j.castSucc,false)
  change (W).endOf ((W).wire (BandGraft.mirrorOutput (A) q (B) j.castSucc)).val=_ at hh
  erw [BandGraft.wire_mirror] at hh
  exact hh
/-- Adjacent reflected ports attach to the same seam. -/
def MirrorAdjacentSeamsAgree : Prop :=
  ∀ (j : Fin w.shape.atomicBand.length),
    ((C).ports.attach ⟨.inr (.inr j.castSucc),(w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output⟩).1=
      ((C).ports.attach ⟨.inr (.inr j.succ),(w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input⟩).1
lemma mirrorAdjacentSame : D.MirrorAdjacentSeamsAgree q w := by
  intro j
  change
    ((C).ports.attach ⟨.inr (.inr j.castSucc),(w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output⟩).1=
      ((C).ports.attach ⟨.inr (.inr j.succ),(w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input⟩).1
  exact (congrArg Prod.fst (D.mirrorOutput_attach q w j.castSucc)).trans
    (congrArg Prod.fst (D.mirrorInput_attach q w j)).symm
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

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
/-- The child identifications across every reflected internal seam. -/
def MirrorChildrenMatch : Prop :=
  ∀ (j : Fin w.shape.atomicBand.length),
    (C).portChildMatch
      ⟨.inr (.inr j.castSucc),(w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output⟩
      ⟨.inr (.inr j.succ),(w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input⟩
      (D.mirrorAdjacentSame q w j)=w.mirrorInteriorChild j
lemma mirrorChildMatch : D.MirrorChildrenMatch q w := by
  intro j
  change
    (C).portChildMatch
      ⟨.inr (.inr j.castSucc),(w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output⟩
      ⟨.inr (.inr j.succ),(w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input⟩
      (D.mirrorAdjacentSame q w j)=w.mirrorInteriorChild j
  exact (C).portChildMatch_eq_of_enumeration _ _ (D.mirrorAdjacentSame q w j)
    (w.mirrorInteriorChild j) (w.mirrorInteriorChild_enumeration j)
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (D : Diagram F S V arity)
lemma frameValues_eq_of_matched_ports (f : D.PortFrames (R:=R))
    (p u : LocalPort V D.ports.kind) (s : S) (b d : Bool)
    (hp : D.ports.attach p=(s,b)) (hu : D.ports.attach u=(s,d))
    (h : (D.ports.attach p).1=(D.ports.attach u).1)
    (hs : (f u).reindex (D.portColumnMatch p u h) (D.portParentMatch p u h)=f p) :
    D.frameValues f s b=D.frameValues f s d := by
  have hh := D.frameValues_match f p u h hs
  have aux {a c : S × Bool} (ha : a=(s,b)) (hc : c=(s,d))
      (he : a.1=c.1)
      (ht : rebaseUnit (congrArg D.seamDim he).symm
        (D.frameValues f c.1 c.2)=D.frameValues f a.1 a.2) :
      D.frameValues f s b=D.frameValues f s d := by
    subst a
    subst c
    simpa only [rebaseUnit_refl] using ht.symm
  exact aux hp hu h hh
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
    (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "FF" => D.namedCutPortFrames q w old T
/-- Compatibility of the transported frames across a reflected internal seam. -/
def MirrorFrameMatch (j : Fin w.shape.atomicBand.length) : Prop :=
    ((FF) ⟨.inr (.inr j.succ),(w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input⟩).reindex
      ((C).portColumnMatch
        ⟨.inr (.inr j.castSucc),(w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output⟩
        ⟨.inr (.inr j.succ),(w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input⟩ (D.mirrorAdjacentSame q w j))
      ((C).portParentMatch
        ⟨.inr (.inr j.castSucc),(w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output⟩
        ⟨.inr (.inr j.succ),(w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input⟩ (D.mirrorAdjacentSame q w j))=
      (FF) ⟨.inr (.inr j.castSucc),(w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output⟩
lemma mirrorFrameMatch (j : Fin w.shape.atomicBand.length) : D.MirrorFrameMatch q w old T j := by
  change
    ((FF) ⟨.inr (.inr j.succ),(w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input⟩).reindex
      ((C).portColumnMatch
        ⟨.inr (.inr j.castSucc),(w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output⟩
        ⟨.inr (.inr j.succ),(w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input⟩ (D.mirrorAdjacentSame q w j))
      ((C).portParentMatch
        ⟨.inr (.inr j.castSucc),(w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output⟩
        ⟨.inr (.inr j.succ),(w.shape.atomicBand.kind j.succ).mirrorPort (w.shape.atomicBand.kind j.succ).input⟩ (D.mirrorAdjacentSame q w j))=
      (FF) ⟨.inr (.inr j.castSucc),(w.shape.atomicBand.kind j.castSucc).mirrorPort (w.shape.atomicBand.kind j.castSucc).output⟩
  exact (C).transported_portFrame_match _ _ (D.mirrorAdjacentSame q w j)
    (D.namedCut_mirror_localRanks q w j.castSucc) (D.namedCut_mirror_localRanks q w j.succ)
    (w.mirrorVertexFrames T j.castSucc) (w.mirrorVertexFrames T j.succ) (w.mirrorInteriorChild j)
    (D.mirrorChildMatch q w j).symm
    (fun a => (w.shape.vertexAtoms j.castSucc).mirror.rank_of_atoms (w.shape.vertexAtoms j.succ).mirror
      (congrArg w.shape.facetAtoms (w.mirror_interior_child j a)))
    ((w.shape.vertexAtoms j.castSucc).mirror.rank_of_atoms (w.shape.vertexAtoms j.succ).mirror
      (congrArg w.shape.facetAtoms (w.mirror_interior_parent j)))
    (w.mirror_interior_frame_seam T j)
/-- Equality of the two frame values on a reflected internal seam. -/
def MirrorFrameValuesAgree (j : Fin w.shape.atomicBand.length) : Prop :=
    (C).frameValues (FF)
      (BandGraft.mirrorOutput
        (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
        (D.ports.refinedBandForSeam q w.shape) j.castSucc) false=
    (C).frameValues (FF)
      (BandGraft.mirrorOutput
        (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
        (D.ports.refinedBandForSeam q w.shape) j.castSucc) true
lemma mirrorFrameValues_eq (j : Fin w.shape.atomicBand.length) : D.MirrorFrameValuesAgree q w old T j := by
  change
    (C).frameValues (FF)
      (BandGraft.mirrorOutput
        (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
        (D.ports.refinedBandForSeam q w.shape) j.castSucc) false=
    (C).frameValues (FF)
      (BandGraft.mirrorOutput
        (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
        (D.ports.refinedBandForSeam q w.shape) j.castSucc) true
  exact ((C).frameValues_eq_of_matched_ports (FF) _ _ _ true false
    (D.mirrorOutput_attach q w j.castSucc) (D.mirrorInput_attach q w j)
    (D.mirrorAdjacentSame q w j) (D.mirrorFrameMatch q w old T j)).symm
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K R : Type} {arity : S → ℕ} [Field K] [CommRing R]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
    (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
variable (φ : R →+* K) (side : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (handle : (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks).HandleValues (R:=K))
local notation "gg" => valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
  (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handle
/-- The framed flag equations on every reflected internal seam. -/
def MirrorInternalFlagsHold : Prop :=
  ∀ (handles : (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks).HandleValues (R:=K))
    (j : Fin w.shape.atomicBand.length),
    SameFramedFlag ((C).seamGrade (BandGraft.mirrorOutput (A) q (B) j.castSucc))
      (matrixUnitEquiv (((C).seamLeft (BandGraft.mirrorOutput (A) q (B) j.castSucc)).eval φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles)))
      (matrixUnitEquiv (((C).seamRight (BandGraft.mirrorOutput (A) q (B) j.castSucc)).eval φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles)))
lemma mirrorInternal_seamHolds : D.MirrorInternalFlagsHold q w old T φ side J Y := by
  intro handles j
  change
    SameFramedFlag ((C).seamGrade (BandGraft.mirrorOutput (A) q (B) j.castSucc))
      (matrixUnitEquiv (((C).seamLeft (BandGraft.mirrorOutput (A) q (B) j.castSucc)).eval φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles)))
      (matrixUnitEquiv (((C).seamRight (BandGraft.mirrorOutput (A) q (B) j.castSucc)).eval φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles)))
  exact (C).trivialSides_seamHolds φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles) _
    (D.refinedCutSideValues_mirror_castSucc q w.shape rfl w.rowRanks w.colRanks side J Y j none)
    (fun i => D.refinedCutSideValues_mirror_castSucc q w.shape rfl w.rowRanks w.colRanks side J Y j (some i))
    (D.mirrorFrameValues_eq q w old T j)
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace PortPatch
variable {V I A B : Type} {kind : V → Kind} (P : PortPatch kind I A B) (a₀ : A) (b₀ : B)
lemma double_plus_branch (a : {a : A // a≠a₀}) :
    (P.double a₀ b₀).plus (.inl (.inr (.inl a)))=
      sumPortAt kind (mirrorKind kind) true (.inl (P.plus (.inr a.val))) := rfl
lemma double_minus_branch (a : {a : A // a≠a₀}) :
    (P.double a₀ b₀).minus (.inl (.inr (.inl a)))=
      sumPortAt kind (mirrorKind kind) false (.inr (mirrorPortAt kind true (P.plus (.inr a.val)))) := rfl
lemma double_plus_branch_neg (b : {b : B // b≠b₀}) :
    (P.double a₀ b₀).plus (.inl (.inr (.inr b)))=
      sumPortAt kind (mirrorKind kind) true (.inr (mirrorPortAt kind false (P.minus (.inr b.val)))) := rfl
lemma double_minus_branch_neg (b : {b : B // b≠b₀}) :
    (P.double a₀ b₀).minus (.inl (.inr (.inr b)))=
      sumPortAt kind (mirrorKind kind) false (.inl (P.minus (.inr b.val))) := rfl
end PortPatch
namespace BandGraft
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
noncomputable abbrev PositiveBranch :=
    {a : {p : PortAt B.kind true // p∉Set.range (VariableGallery.internalPlus B.kind)} // a≠B.shortFirst}
noncomputable abbrev NegativeBranch :=
    {b : {p : PortAt B.kind false // p∉Set.range (VariableGallery.internalMinus B.kind)} // b≠B.shortLast}
noncomputable def branchPlus (a : PositiveBranch A q B) :=
  graftPlus A B.doublePatch (.inr (.inl (.inr (.inl a))))
noncomputable def branchMinus (a : PositiveBranch A q B) :=
  graftMinus A B.doublePatch (.inr (.inl (.inr (.inl a))))
noncomputable def branchNegPlus (b : NegativeBranch A q B) :=
  graftPlus A B.doublePatch (.inr (.inl (.inr (.inr b))))
noncomputable def branchNegMinus (b : NegativeBranch A q B) :=
  graftMinus A B.doublePatch (.inr (.inl (.inr (.inr b))))
lemma wire_branchPlus (a : PositiveBranch A q B) :
    (wiring A q B).wire (branchPlus A q B a)=branchMinus A q B a := by
  exact graft_wire_plus A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl)
    (.inr (.inl (.inr (.inl a))))
lemma wire_branchNegPlus (b : NegativeBranch A q B) :
    (wiring A q B).wire (branchNegPlus A q B b)=branchNegMinus A q B b := by
  exact graft_wire_plus A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl)
    (.inr (.inl (.inr (.inr b))))
end BandGraft
end IntegralCharacterVarieties.OccurrenceIncidence
end

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.VariableGallery
open scoped Classical
open VertexTable
variable {l : ℕ} (kind : Fin (l+1) → Kind)
lemma positive_not_output (p : PortAt kind true) : p.val.2≠(kind p.val.1).output := by
  intro h
  have hp := p.property
  rw [h,(kind p.val.1).output_endpoint] at hp
  contradiction
lemma negative_not_input (p : PortAt kind false) : p.val.2≠(kind p.val.1).input := by
  intro h
  have hp := p.property
  rw [h,(kind p.val.1).input_endpoint] at hp
  contradiction
lemma exposed_positive_not_input
    (p : PortAt kind true) (hi : p∉Set.range (internalPlus kind))
    (h0 : p≠input kind 0) : p.val.2≠(kind p.val.1).input := by
  intro hh
  have he : p=input kind p.val.1 := by
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq hh)
  have hvertex (v : Fin (l+1)) : input kind v=input kind 0 ∨ input kind v∈Set.range (internalPlus kind) := by
    refine Fin.cases (Or.inl rfl) (fun j => ?_) v
    exact Or.inr ⟨j,rfl⟩
  rcases hvertex p.val.1 with hz|hz
  · exact h0 (he.trans hz)
  · exact hi (he ▸ hz)
lemma exposed_negative_not_output
    (p : PortAt kind false) (hi : p∉Set.range (internalMinus kind))
    (h0 : p≠output kind (Fin.last l)) : p.val.2≠(kind p.val.1).output := by
  intro hh
  have he : p=output kind p.val.1 := by
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq hh)
  have hvertex (v : Fin (l+1)) : output kind v=output kind (Fin.last l) ∨ output kind v∈Set.range (internalMinus kind) := by
    refine Fin.lastCases (Or.inl rfl) (fun j => ?_) v
    exact Or.inr ⟨j,rfl⟩
  rcases hvertex p.val.1 with hz|hz
  · exact h0 (he.trans hz)
  · exact hi (he ▸ hz)
end IntegralCharacterVarieties.OccurrenceIncidence.VariableGallery
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression NamedBandGrades VertexTable
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "W" => BandGraft.wiring (A) q (B)
variable (a : BandGraft.PositiveBranch
  (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
  (D.ports.refinedBandForSeam q w.shape))
/-- The attachment of the original port of a positive transverse branch. -/
def PositiveBranchOriginalAttached : Prop :=
  ∀ (a : BandGraft.PositiveBranch
      (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
      (D.ports.refinedBandForSeam q w.shape)),
    (C).ports.attach ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩=(BandGraft.branchPlus (A) q (B) a,true)
lemma branchPos_original_attach : D.PositiveBranchOriginalAttached q w := by
  intro a
  change
    (C).ports.attach ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩=(BandGraft.branchPlus (A) q (B) a,true)
  exact (W).endOf_portAt (BandGraft.branchPlus (A) q (B) a,true)
/-- The attachment of the reflected port of a positive transverse branch. -/
def PositiveBranchMirrorAttached : Prop :=
  ∀ (a : BandGraft.PositiveBranch
      (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
      (D.ports.refinedBandForSeam q w.shape)),
    (C).ports.attach ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩=(BandGraft.branchPlus (A) q (B) a,false)
lemma branchPos_mirror_attach : D.PositiveBranchMirrorAttached q w := by
  intro a
  change
    (C).ports.attach ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩=(BandGraft.branchPlus (A) q (B) a,false)
  have hh := (W).endOf_portAt (BandGraft.branchPlus (A) q (B) a,false)
  change (W).endOf ((W).wire (BandGraft.branchPlus (A) q (B) a)).val=_ at hh
  erw [BandGraft.wire_branchPlus] at hh
  exact hh
/-- The two ports of each positive transverse branch attach to the same seam. -/
def PositiveBranchSameSeam : Prop :=
  ∀ (a : BandGraft.PositiveBranch
      (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
      (D.ports.refinedBandForSeam q w.shape)),
    ((C).ports.attach ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩).1=
    ((C).ports.attach ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩).1
lemma branchPos_same : D.PositiveBranchSameSeam q w := by
  intro a
  change
    ((C).ports.attach ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩).1=
    ((C).ports.attach ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩).1
  exact (congrArg Prod.fst (branchPos_original_attach D q w a)).trans
    (congrArg Prod.fst (branchPos_mirror_attach D q w a)).symm
omit [Finite V] in
lemma branchPos_not_input : (a.val.val.val.2)≠((w.shape.atomicBand.kind (a.val.val.val.1))).input := by
  apply VariableGallery.exposed_positive_not_input (B).kind a.val.val a.val.property
  intro hh
  exact a.property (Subtype.ext hh)
omit [Finite V] in
lemma branchPos_not_output : (a.val.val.val.2)≠((w.shape.atomicBand.kind (a.val.val.val.1))).output :=
  VariableGallery.positive_not_output (B).kind a.val.val
/-- The child identifications along each positive transverse branch. -/
def PositiveBranchChildrenMatch : Prop :=
  ∀ (a : BandGraft.PositiveBranch
      (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
      (D.ports.refinedBandForSeam q w.shape)),
    (C).portChildMatch ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩ ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩
      (branchPos_same D q w a)=((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorChild (a.val.val.val.2)
lemma branchPos_childMatch : D.PositiveBranchChildrenMatch q w := by
  intro a
  change
    (C).portChildMatch ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩ ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩
      (branchPos_same D q w a)=((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorChild (a.val.val.val.2)
  apply (C).portChildMatch_eq_of_enumeration
  intro c
  exact congrArg Fin.val (((w.shape.atomicBand.kind (a.val.val.val.1))).mirror_childEnumeration (a.val.val.val.2) c)
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression NamedBandGrades VertexTable
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "W" => BandGraft.wiring (A) q (B)
variable (a : BandGraft.PositiveBranch
  (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
  (D.ports.refinedBandForSeam q w.shape))
variable (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
local notation "FF" => D.namedCutPortFrames q w old T
/-- Compatibility of the transported frames across a positive transverse branch. -/
def PositiveBranchFrameMatch : Prop :=
    ((FF) ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩).reindex
      ((C).portColumnMatch ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩ ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩ (D.branchPos_same q w a))
      ((C).portParentMatch ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩ ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩ (D.branchPos_same q w a))=
      (FF) ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩
lemma branchPosFrameMatch : D.PositiveBranchFrameMatch q w a old T := by
  change
    ((FF) ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩).reindex
      ((C).portColumnMatch ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩ ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩ (D.branchPos_same q w a))
      ((C).portParentMatch ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩ ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩ (D.branchPos_same q w a))=
      (FF) ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩
  exact (C).transported_portFrame_match _ _ (D.branchPos_same q w a)
    (D.namedCut_orig_localRanks q w (a.val.val.val.1)) (D.namedCut_mirror_localRanks q w (a.val.val.val.1))
    (w.vertexFrames (a.val.val.val.1)) (w.mirrorVertexFrames T (a.val.val.val.1)) (((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorChild (a.val.val.val.2))
    (D.branchPos_childMatch q w a).symm
    (fun c => (w.shape.vertexAtoms (a.val.val.val.1)).rank_of_atoms (w.shape.vertexAtoms (a.val.val.val.1)).mirror
      ((w.shape.vertexAtoms (a.val.val.val.1)).mirror_atoms ⟨(a.val.val.val.2),some c⟩).symm)
    ((w.shape.vertexAtoms (a.val.val.val.1)).rank_of_atoms (w.shape.vertexAtoms (a.val.val.val.1)).mirror
      ((w.shape.vertexAtoms (a.val.val.val.1)).mirror_atoms ⟨(a.val.val.val.2),none⟩).symm)
    (w.transverse_frame_seam T (a.val.val.val.1) (a.val.val.val.2) (D.branchPos_not_input q w a) (D.branchPos_not_output q w a))
/-- Equality of the two frame values on a positive transverse branch. -/
def PositiveBranchFrameValuesAgree : Prop :=
    (C).frameValues (FF) (BandGraft.branchPlus (A) q (B) a) false=
    (C).frameValues (FF) (BandGraft.branchPlus (A) q (B) a) true
lemma branchPosFrameValues_eq : D.PositiveBranchFrameValuesAgree q w a old T := by
  change
    (C).frameValues (FF) (BandGraft.branchPlus (A) q (B) a) false=
    (C).frameValues (FF) (BandGraft.branchPlus (A) q (B) a) true
  exact ((C).frameValues_eq_of_matched_ports (FF) _ _ _ true false
    (D.branchPos_original_attach q w a) (D.branchPos_mirror_attach q w a)
    (D.branchPos_same q w a) (D.branchPosFrameMatch q w a old T)).symm
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression NamedBandGrades VertexTable
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "W" => BandGraft.wiring (A) q (B)
variable (a : BandGraft.NegativeBranch
  (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
  (D.ports.refinedBandForSeam q w.shape))
/-- The attachment of the original port of a negative transverse branch. -/
def NegativeBranchOriginalAttached : Prop :=
  ∀ (a : BandGraft.NegativeBranch
      (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
      (D.ports.refinedBandForSeam q w.shape)),
    (C).ports.attach ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩=(BandGraft.branchNegPlus (A) q (B) a,false)
lemma branchNeg_original_attach : D.NegativeBranchOriginalAttached q w := by
  intro a
  change
    (C).ports.attach ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩=(BandGraft.branchNegPlus (A) q (B) a,false)
  have hh := (W).endOf_portAt (BandGraft.branchNegPlus (A) q (B) a,false)
  change (W).endOf ((W).wire (BandGraft.branchNegPlus (A) q (B) a)).val=_ at hh
  erw [BandGraft.wire_branchNegPlus] at hh
  exact hh
/-- The attachment of the reflected port of a negative transverse branch. -/
def NegativeBranchMirrorAttached : Prop :=
  ∀ (a : BandGraft.NegativeBranch
      (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
      (D.ports.refinedBandForSeam q w.shape)),
    (C).ports.attach ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩=(BandGraft.branchNegPlus (A) q (B) a,true)
lemma branchNeg_mirror_attach : D.NegativeBranchMirrorAttached q w := by
  intro a
  change
    (C).ports.attach ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩=(BandGraft.branchNegPlus (A) q (B) a,true)
  exact (W).endOf_portAt (BandGraft.branchNegPlus (A) q (B) a,true)
/-- The two ports of each negative transverse branch attach to the same seam. -/
def NegativeBranchSameSeam : Prop :=
  ∀ (a : BandGraft.NegativeBranch
      (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
      (D.ports.refinedBandForSeam q w.shape)),
    ((C).ports.attach ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩).1=
    ((C).ports.attach ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩).1
lemma branchNeg_same : D.NegativeBranchSameSeam q w := by
  intro a
  change
    ((C).ports.attach ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩).1=
    ((C).ports.attach ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩).1
  exact (congrArg Prod.fst (branchNeg_original_attach D q w a)).trans
    (congrArg Prod.fst (branchNeg_mirror_attach D q w a)).symm
omit [Finite V] in
lemma branchNeg_not_input : (a.val.val.val.2)≠((w.shape.atomicBand.kind (a.val.val.val.1))).input :=
  VariableGallery.negative_not_input (B).kind a.val.val
omit [Finite V] in
lemma branchNeg_not_output : (a.val.val.val.2)≠((w.shape.atomicBand.kind (a.val.val.val.1))).output := by
  apply VariableGallery.exposed_negative_not_output (B).kind a.val.val a.val.property
  intro hh
  exact a.property (Subtype.ext hh)
/-- The child identifications along each negative transverse branch. -/
def NegativeBranchChildrenMatch : Prop :=
  ∀ (a : BandGraft.NegativeBranch
      (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
      (D.ports.refinedBandForSeam q w.shape)),
    (C).portChildMatch ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩ ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩
      (branchNeg_same D q w a)=((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorChild (a.val.val.val.2)
lemma branchNeg_childMatch : D.NegativeBranchChildrenMatch q w := by
  intro a
  change
    (C).portChildMatch ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩ ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩
      (branchNeg_same D q w a)=((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorChild (a.val.val.val.2)
  apply (C).portChildMatch_eq_of_enumeration
  intro c
  exact congrArg Fin.val (((w.shape.atomicBand.kind (a.val.val.val.1))).mirror_childEnumeration (a.val.val.val.2) c)
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence MatrixExpression NamedBandGrades VertexTable
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "W" => BandGraft.wiring (A) q (B)
variable (a : BandGraft.NegativeBranch
  (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
  (D.ports.refinedBandForSeam q w.shape))
variable (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
local notation "FF" => D.namedCutPortFrames q w old T
/-- Compatibility of the transported frames across a negative transverse branch. -/
def NegativeBranchFrameMatch : Prop :=
    ((FF) ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩).reindex
      ((C).portColumnMatch ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩ ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩ (D.branchNeg_same q w a))
      ((C).portParentMatch ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩ ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩ (D.branchNeg_same q w a))=
      (FF) ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩
lemma branchNegFrameMatch : D.NegativeBranchFrameMatch q w a old T := by
  change
    ((FF) ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩).reindex
      ((C).portColumnMatch ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩ ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩ (D.branchNeg_same q w a))
      ((C).portParentMatch ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩ ⟨.inr (.inr (a.val.val.val.1)),((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorPort (a.val.val.val.2)⟩ (D.branchNeg_same q w a))=
      (FF) ⟨.inr (.inl (a.val.val.val.1)),(a.val.val.val.2)⟩
  exact (C).transported_portFrame_match _ _ (D.branchNeg_same q w a)
    (D.namedCut_orig_localRanks q w (a.val.val.val.1)) (D.namedCut_mirror_localRanks q w (a.val.val.val.1))
    (w.vertexFrames (a.val.val.val.1)) (w.mirrorVertexFrames T (a.val.val.val.1)) (((w.shape.atomicBand.kind (a.val.val.val.1))).mirrorChild (a.val.val.val.2))
    (D.branchNeg_childMatch q w a).symm
    (fun c => (w.shape.vertexAtoms (a.val.val.val.1)).rank_of_atoms (w.shape.vertexAtoms (a.val.val.val.1)).mirror
      ((w.shape.vertexAtoms (a.val.val.val.1)).mirror_atoms ⟨(a.val.val.val.2),some c⟩).symm)
    ((w.shape.vertexAtoms (a.val.val.val.1)).rank_of_atoms (w.shape.vertexAtoms (a.val.val.val.1)).mirror
      ((w.shape.vertexAtoms (a.val.val.val.1)).mirror_atoms ⟨(a.val.val.val.2),none⟩).symm)
    (w.transverse_frame_seam T (a.val.val.val.1) (a.val.val.val.2) (D.branchNeg_not_input q w a) (D.branchNeg_not_output q w a))
/-- Equality of the two frame values on a negative transverse branch. -/
def NegativeBranchFrameValuesAgree : Prop :=
    (C).frameValues (FF) (BandGraft.branchNegPlus (A) q (B) a) false=
    (C).frameValues (FF) (BandGraft.branchNegPlus (A) q (B) a) true
lemma branchNegFrameValues_eq : D.NegativeBranchFrameValuesAgree q w a old T := by
  change
    (C).frameValues (FF) (BandGraft.branchNegPlus (A) q (B) a) false=
    (C).frameValues (FF) (BandGraft.branchNegPlus (A) q (B) a) true
  exact (C).frameValues_eq_of_matched_ports (FF) _ _ _ false true
    (D.branchNeg_original_attach q w a) (D.branchNeg_mirror_attach q w a)
    (D.branchNeg_same q w a) (D.branchNegFrameMatch q w a old T)
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable TwoFlagBand NamedBandGrades
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {r : ℕ} (d : RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
local notation "B" => D.ports.refinedBandForSeam q d
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)
local notation "W" => BandGraft.wiring (A) q (B)
variable (old : D.SideValues (R:=R))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩))) (Fin (D.rank (D.ports.facet ⟨q,none⟩))) R)ˣ)
/-- The side values on each positive transverse branch are trivial. -/
def PositiveBranchSideValuesTrivial : Prop :=
  ∀ (a : BandGraft.PositiveBranch (A) q (B))
    (i : Option (Fin ((W).seamArity (BandGraft.branchPlus (A) q (B) a)))),
    D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨BandGraft.branchPlus (A) q (B) a,i⟩=1
lemma refinedCutSideValues_branchPos : D.PositiveBranchSideValuesTrivial q d hp hc hc' old J Y := by
  intro a i
  change
    D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨BandGraft.branchPlus (A) q (B) a,i⟩=1
  exact graftSideValues_internal (A) (B).doublePatch (doubleDecoration (B).decoration) q
    ((B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast)
    (fun i => by rw [(B).double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [(B).double_signature_minus]; cases i <;> rfl)
    (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J) (D.cutShortSideValues q Y)
    (.inr (.inl a)) i
/-- The side values on each negative transverse branch are trivial. -/
def NegativeBranchSideValuesTrivial : Prop :=
  ∀ (b : BandGraft.NegativeBranch (A) q (B))
    (i : Option (Fin ((W).seamArity (BandGraft.branchNegPlus (A) q (B) b)))),
    D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨BandGraft.branchNegPlus (A) q (B) b,i⟩=1
lemma refinedCutSideValues_branchNeg : D.NegativeBranchSideValuesTrivial q d hp hc hc' old J Y := by
  intro b i
  change
    D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨BandGraft.branchNegPlus (A) q (B) b,i⟩=1
  exact graftSideValues_internal (A) (B).doublePatch (doubleDecoration (B).decoration) q
    ((B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast)
    (fun i => by rw [(B).double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [(B).double_signature_minus]; cases i <;> rfl)
    (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J) (D.cutShortSideValues q Y)
    (.inr (.inr b)) i
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K R : Type} {arity : S → ℕ} [Field K] [CommRing R]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
    (old : D.PortFrames (R:=K))
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
variable (φ : R →+* K) (side : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
    (handle : (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks).HandleValues (R:=K))
local notation "gg" => valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
  (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handle
/-- The framed flag equations on each positive transverse branch. -/
def PositiveBranchFlagsHold : Prop :=
  ∀ (handles : (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks).HandleValues (R:=K))
    (a : BandGraft.PositiveBranch
      (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
      (D.ports.refinedBandForSeam q w.shape)),
    SameFramedFlag ((C).seamGrade (BandGraft.branchPlus (A) q (B) a))
      (matrixUnitEquiv (((C).seamLeft (BandGraft.branchPlus (A) q (B) a)).eval φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles)))
      (matrixUnitEquiv (((C).seamRight (BandGraft.branchPlus (A) q (B) a)).eval φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles)))
lemma branchPos_seamHolds : D.PositiveBranchFlagsHold q w old T φ side J Y := by
  intro handles a
  change
    SameFramedFlag ((C).seamGrade (BandGraft.branchPlus (A) q (B) a))
      (matrixUnitEquiv (((C).seamLeft (BandGraft.branchPlus (A) q (B) a)).eval φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles)))
      (matrixUnitEquiv (((C).seamRight (BandGraft.branchPlus (A) q (B) a)).eval φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles)))
  exact (C).trivialSides_seamHolds φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles) _
    (D.refinedCutSideValues_branchPos q w.shape rfl w.rowRanks w.colRanks side J Y a none)
    (fun i => D.refinedCutSideValues_branchPos q w.shape rfl w.rowRanks w.colRanks side J Y a (some i))
    (D.branchPosFrameValues_eq q w a old T)

/-- The framed flag equations on each negative transverse branch. -/
def NegativeBranchFlagsHold : Prop :=
  ∀ (handles : (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks).HandleValues (R:=K))
    (a : BandGraft.NegativeBranch
      (D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)) q
      (D.ports.refinedBandForSeam q w.shape)),
    SameFramedFlag ((C).seamGrade (BandGraft.branchNegPlus (A) q (B) a))
      (matrixUnitEquiv (((C).seamLeft (BandGraft.branchNegPlus (A) q (B) a)).eval φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles)))
      (matrixUnitEquiv (((C).seamRight (BandGraft.branchNegPlus (A) q (B) a)).eval φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles)))
lemma branchNeg_seamHolds : D.NegativeBranchFlagsHold q w old T φ side J Y := by
  intro handles a
  change
    SameFramedFlag ((C).seamGrade (BandGraft.branchNegPlus (A) q (B) a))
      (matrixUnitEquiv (((C).seamLeft (BandGraft.branchNegPlus (A) q (B) a)).eval φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles)))
      (matrixUnitEquiv (((C).seamRight (BandGraft.branchNegPlus (A) q (B) a)).eval φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles)))
  exact (C).trivialSides_seamHolds φ (valuesFromPorts (D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks) (D.namedCutPortFrames q w old T)
        (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handles) _
    (D.refinedCutSideValues_branchNeg q w.shape rfl w.rowRanks w.colRanks side J Y a none)
    (fun i => D.refinedCutSideValues_branchNeg q w.shape rfl w.rowRanks w.colRanks side J Y a (some i))
    (D.branchNegFrameValues_eq q w a old T)
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
