import OAI.AlgebraicGeometry.CharacterVarieties.Frames.MarkedFrames
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.FrameTransport
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.SeamCoordinates

namespace OAI

/-!
# The first short seam

Port coordinates transport the old negative framed flag to the first short
seam of a marked cut.
-/

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades
private lemma transportFirstFrames_coordinates
    {K I J : Type} [CommRing K] [Fintype I] [Fintype J]
    {k : Kind} {d d' : LocalRanks k} (hd : d=d')
    (f : (p : k.table.Port) → MatrixIso K (d.Columns p) (d.Parent p))
    (p : k.table.Port) (e : I ≃ d.Columns p) (r : J ≃ d.Parent p) :
    ((LocalRanks.transportFrames hd f p).reindex
      (e.trans (LocalRanks.columnCongr hd p))
      (r.trans (LocalRanks.parentCongr hd p))).linearEquiv =
      ((f p).reindex e r).linearEquiv := by
  have hh := congrArg (fun z : MatrixIso K (d.Columns p) (d.Parent p) =>
      (z.reindex e r).linearEquiv) (LocalRanks.transportFrames_reindex hd f p)
  simpa only [MatrixIso.reindex_reindex_eq] using hh

variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    {h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) (D.namedSeamFrame q (g (.frame q false))) h)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "FF" => D.namedCutPortFrames q w (D.portFrame g) T
local notation "oo" => D.ports.attach.symm (q,false)
local notation "ho" => Eq.symm (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (Sigma.fst (D.ports.attach.symm (q,false))))
local notation "hn" => D.namedCut_orig_localRanks q w 0
local notation "pp" => Kind.input (w.shape.atomicBand.kind 0)
/-- The old negative port frame has the original named seam coordinates. -/
def FirstOldFrameCoordinates : Prop :=
    (((FF) ⟨.inl (oo).1,(oo).2⟩).reindex
      (D.cutFirstOldActualColumns q w) (D.cutFirstOldActualRows q w)).linearEquiv=
      D.namedSeamFrame q (g (.frame q false))
lemma cutFirst_old_frameCoordinates : D.FirstOldFrameCoordinates q g w T := by
  change
    (((FF) ⟨.inl (oo).1,(oo).2⟩).reindex
      (D.cutFirstOldActualColumns q w) (D.cutFirstOldActualRows q w)).linearEquiv=
      D.namedSeamFrame q (g (.frame q false))
  convert! (transportFirstFrames_coordinates (ho)
    (fun p => D.portFrame g ⟨(oo).1,p⟩) (oo).2
    (D.cutFirstOldColumns q) (D.cutFirstOldRows q)).trans
      (D.portFrame_namedCoordinates g (oo) q false
        (D.ports.attach.apply_symm_apply (q,false))) using 1
/-- The first new port frame has the coordinates of the identified band. -/
def FirstNewFrameCoordinates : Prop :=
    (((FF) ⟨.inr (.inl 0),(pp)⟩).reindex
      (D.cutFirstNewActualColumns q w) (D.cutFirstNewActualRows q w)).linearEquiv=w.firstFrame
lemma cutFirst_new_frameCoordinates : D.FirstNewFrameCoordinates q g w T := by
  change
    (((FF) ⟨.inr (.inl 0),(pp)⟩).reindex
      (D.cutFirstNewActualColumns q w) (D.cutFirstNewActualRows q w)).linearEquiv=w.firstFrame
  convert! transportFirstFrames_coordinates (hn) (w.vertexFrames 0) (pp)
    w.firstColumns.symm (finCongr w.firstParent_rank).symm using 1
/-- The first short seam uses the grade of the original child index. -/
def FirstSeamGrade : Prop :=
  ∀ (i : (i : Fin (arity q)) × Fin (D.childDim q i)),
    (C).seamGrade ((C).ports.attach ⟨.inl (oo).1,(oo).2⟩).1
      ((C).portColumnIndex ⟨.inl (oo).1,(oo).2⟩ (D.cutFirstOldActualColumns q w i))=i.1.val
lemma cutFirst_grade : D.FirstSeamGrade q g w := by
  intro i
  change
    (C).seamGrade ((C).ports.attach ⟨.inl (oo).1,(oo).2⟩).1
      ((C).portColumnIndex ⟨.inl (oo).1,(oo).2⟩ (D.cutFirstOldActualColumns q w i))=i.1.val
  rw [(C).seamGrade_portColumnIndex]
  change (((D.ports.kind (oo).1).childEnumeration (oo).2)
    ((D.ports.childEquiv (oo)).symm ((finCongr (congrArg arity
      (congrArg Prod.fst (D.ports.attach.apply_symm_apply (q,false))))).symm i.1))).val=_
  simp only [PortAssembly.childEquiv,Equiv.symm_trans_apply,Equiv.apply_symm_apply]
  rfl
/-- The local frames at the first short seam determine the same graded flag. -/
def FirstLocalFrameFlag : Prop :=
    SameFramedFlag (fun i => (C).seamGrade ((C).ports.attach ⟨.inl (oo).1,(oo).2⟩).1
      ((C).portColumnIndex ⟨.inl (oo).1,(oo).2⟩ i))
      ((FF) ⟨.inl (oo).1,(oo).2⟩).linearEquiv
      (((FF) ⟨.inr (.inl 0),(pp)⟩).reindex
        ((C).portColumnMatch ⟨.inl (oo).1,(oo).2⟩ ⟨.inr (.inl 0),(pp)⟩ (D.firstAdjacentSame q w))
        ((C).portParentMatch ⟨.inl (oo).1,(oo).2⟩ ⟨.inr (.inl 0),(pp)⟩ (D.firstAdjacentSame q w))).linearEquiv
lemma cutFirst_localFrameFlag : D.FirstLocalFrameFlag q g w T := by
  change
    SameFramedFlag (fun i => (C).seamGrade ((C).ports.attach ⟨.inl (oo).1,(oo).2⟩).1
      ((C).portColumnIndex ⟨.inl (oo).1,(oo).2⟩ i))
      ((FF) ⟨.inl (oo).1,(oo).2⟩).linearEquiv
      (((FF) ⟨.inr (.inl 0),(pp)⟩).reindex
        ((C).portColumnMatch ⟨.inl (oo).1,(oo).2⟩ ⟨.inr (.inl 0),(pp)⟩ (D.firstAdjacentSame q w))
        ((C).portParentMatch ⟨.inl (oo).1,(oo).2⟩ ⟨.inr (.inl 0),(pp)⟩ (D.firstAdjacentSame q w))).linearEquiv
  exact MatrixIso.sameFramedFlag_of_matching_coordinates _
    ((FF) ⟨.inl (oo).1,(oo).2⟩) ((FF) ⟨.inr (.inl 0),(pp)⟩)
    ((C).portColumnMatch ⟨.inl (oo).1,(oo).2⟩ ⟨.inr (.inl 0),(pp)⟩ (D.firstAdjacentSame q w))
    ((C).portParentMatch ⟨.inl (oo).1,(oo).2⟩ ⟨.inr (.inl 0),(pp)⟩ (D.firstAdjacentSame q w))
    (D.cutFirstOldActualColumns q w) (D.cutFirstOldActualRows q w)
    (D.cutFirstNewActualColumns q w) (D.cutFirstNewActualRows q w)
    (D.cutFirstColumn_match q w) (D.cutFirstRow_match q w)
    (fun i : (i : Fin (arity q)) × Fin (D.childDim q i) => i.1.val)
    (D.namedSeamFrame q (g (.frame q false))) w.firstFrame
    (D.cutFirst_grade q g w) (D.cutFirst_old_frameCoordinates q g w T)
    (D.cutFirst_new_frameCoordinates q g w T) w.firstFrame_holds.symm
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical Matrix
open VertexTable SurfacePresentation.Diagram
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
    (rank : F → ℕ)
    (old : (s : Side S arity) → FacetUnit (R:=R) rank (A.facet s))
    (short : Bool → (i : Option (Fin (arity q))) → FacetUnit (R:=R) rank (A.facet ⟨q,i⟩))
lemma bandValues_first_one
    (hshort : ∀ i,short false i=1)
    (i : Option (Fin ((wiring A q B).seamArity (originalPort A q B 0 true)))) :
    bandValues A q B rank old short ⟨originalPort A q B 0 true,i⟩=1 := by
  cases i with
  | none =>
    have hh := originalValue_zero A q B rank old short
    rw [hshort] at hh
    apply (rebaseUnit (congrArg rank (originalSide_color A q B 0))).injective
    exact hh.trans ((rebaseUnit _).map_one).symm
  | some i =>
    exact graftSideValues_short_identity A B.doublePatch (doubleDecoration B.decoration) q
      (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
      (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
      (fun i => by rw [B.double_signature_minus]; cases i <;> rfl) rank old short false i
      (fun j => hshort (some j))
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
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
variable (old : D.SideValues (R:=R))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩))) (Fin (D.rank (D.ports.facet ⟨q,none⟩))) R)ˣ)
/-- All side values at the first short seam are the identity. -/
def FirstShortSideValuesTrivial : Prop :=
  ∀ (i : Option (Fin ((BandGraft.wiring (A) q (B)).seamArity
      (BandGraft.originalPort (A) q (B) 0 true)))),
    D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨BandGraft.originalPort (A) q (B) 0 true,i⟩=1
lemma refinedCutSideValues_first : D.FirstShortSideValuesTrivial q d hp hc hc' old J Y := by
  intro i
  change
    D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨BandGraft.originalPort (A) q (B) 0 true,i⟩=1
  exact BandGraft.bandValues_first_one (A) q (B)
    (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J) (D.cutShortSideValues q Y)
    (fun i => by cases i <;> rfl) i
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression HomTransport
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
    (D : Diagram F S V arity) (φ : R →+* A)
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
/-- Equality of the framed flags gives the first short seam equation. -/
lemma trivialSides_seamHolds_of_flag (s : S)
    (hp : g (.side ⟨s,none⟩)=1)
    (hc : ∀ i,g (.side ⟨s,some i⟩)=1)
    (hf : SameFramedFlag (D.seamGrade s)
      (matrixUnitEquiv (g (.frame s false)))
      (matrixUnitEquiv (g (.frame s true)))) :
    SameFramedFlag (D.seamGrade s)
      (matrixUnitEquiv ((D.seamLeft s).eval φ g))
      (matrixUnitEquiv ((D.seamRight s).eval φ g)) := by
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
  simp only [seamLeft,seamRight,Term.eval,ha',hb,frameWord,Term.eval]
  erw [one_mul,mul_one]
  exact hf
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K R : Type} {arity : S → ℕ} [Field K] [CommRing R]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    {h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) (D.namedSeamFrame q (g (.frame q false))) h)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
variable (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
local notation "C" => D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax
local notation "FF" => D.markedCutFrames q w hproper hmax (D.portFrame g) T
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
variable (φ : R →+* K) (side : D.SideValues (R:=K))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
/-- The first short seam inherits the old negative framed flag for every handle value. -/
def MarkedFirstShortFlag : Prop :=
  ∀ (handle :
      (D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax).HandleValues (R:=K)),
    let gg := valuesFromPorts
      (D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax) (FF)
      (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handle
    SameFramedFlag ((C).seamGrade (BandGraft.originalPort (A) q (B) 0 true))
      (matrixUnitEquiv (((C).seamLeft (BandGraft.originalPort (A) q (B) 0 true)).eval φ (gg)))
      (matrixUnitEquiv (((C).seamRight (BandGraft.originalPort (A) q (B) 0 true)).eval φ (gg)))
lemma markedFirstShort_seamHolds : D.MarkedFirstShortFlag q g w T hproper hmax φ side J Y := by
  intro handle
  let gg := valuesFromPorts
    (D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax) (FF)
    (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks side J Y) handle
  change
    SameFramedFlag ((C).seamGrade (BandGraft.originalPort (A) q (B) 0 true))
      (matrixUnitEquiv (((C).seamLeft (BandGraft.originalPort (A) q (B) 0 true)).eval φ (gg)))
      (matrixUnitEquiv (((C).seamRight (BandGraft.originalPort (A) q (B) 0 true)).eval φ (gg)))
  exact (C).trivialSides_seamHolds_of_flag φ (gg) _
    (D.refinedCutSideValues_first q w.shape rfl w.rowRanks w.colRanks side J Y none)
    (fun i=>D.refinedCutSideValues_first q w.shape rfl w.rowRanks w.colRanks side J Y (some i))
    ((C).frameValues_seam_flag_of_ports (FF) _ _ _
      (D.firstOldNegative_attach q w) (D.origInput_attach q w 0)
      (D.firstAdjacentSame q w) (D.cutFirst_localFrameFlag q g w T))
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
