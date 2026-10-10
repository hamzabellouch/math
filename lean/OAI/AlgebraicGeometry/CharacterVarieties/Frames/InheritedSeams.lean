import OAI.AlgebraicGeometry.CharacterVarieties.Frames.InheritedFrames
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.SeamCoordinates

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h) (s : S)
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks

def cutInheritedSeamColumns : ((i : Fin (arity s)) × Fin (D.childDim s i)) ≃
    Fin ((C).seamDim (D.cutOldSeam q w.shape s)) :=
  (Equiv.sigmaCongr (finCongr (D.cutOldSeam_arity q w.shape s).symm)
    (fun i => finCongr (D.cutOldSideRank q w.shape rfl w.rowRanks w.colRanks s (some i)).symm)).trans
      (blockIndex ((C).childDim (D.cutOldSeam q w.shape s))).symm

def cutInheritedSeamRows : Fin (D.rank (D.ports.facet ⟨s,none⟩)) ≃
    Fin ((C).seamDim (D.cutOldSeam q w.shape s)) :=
  finCongr ((D.cutOldSideRank q w.shape rfl w.rowRanks w.colRanks s none).symm.trans
    ((C).seamRank (D.cutOldSeam q w.shape s)))

/-- Inherited port columns agree with the column coordinates of their cut seam. -/
def CutInheritedSeamColumnCoordinates (b : Bool) (hs : s≠q) : Prop :=
    ((D.cutInheritedColumns q w s b).trans
      ((C).portColumnIndex ⟨.inl (D.ports.attach.symm (s,b)).1,(D.ports.attach.symm (s,b)).2⟩)).trans
      (finCongr (congrArg (C).seamDim (congrArg Prod.fst (D.cutInherited_attach q w s b hs))))=
      D.cutInheritedSeamColumns q w s

lemma cutInheritedSeamColumns_coordinates (b : Bool) (hs : s≠q) :
    D.CutInheritedSeamColumnCoordinates q w s b hs := by
  change ((D.cutInheritedColumns q w s b).trans
    ((C).portColumnIndex ⟨.inl (D.ports.attach.symm (s,b)).1,(D.ports.attach.symm (s,b)).2⟩)).trans
    (finCongr (congrArg (C).seamDim (congrArg Prod.fst (D.cutInherited_attach q w s b hs))))=
    D.cutInheritedSeamColumns q w s
  apply (C).port_coordinates_blockIndex (D.childDim s) _ _ b
    (D.cutInherited_attach q w s b hs)
    (finCongr (D.cutOldSeam_arity q w.shape s).symm)
    (fun i => (D.cutOldSideRank q w.shape rfl w.rowRanks w.colRanks s (some i)).symm)
    (D.cutInheritedColumns q w s b)
  · intro i
    exact D.cutInheritedColumns_childEnumeration q w s b i
  · exact D.cutInheritedColumns_value q w s b

/-- Inherited port rows agree with the row coordinates of their cut seam. -/
def CutInheritedSeamRowCoordinates (b : Bool) (hs : s≠q) : Prop :=
    ((D.cutInheritedRows q w s b).trans
      ((C).portRowIndex ⟨.inl (D.ports.attach.symm (s,b)).1,(D.ports.attach.symm (s,b)).2⟩)).trans
      (finCongr (congrArg (C).seamDim (congrArg Prod.fst (D.cutInherited_attach q w s b hs))))=
      D.cutInheritedSeamRows q w s

lemma cutInheritedSeamRows_coordinates (b : Bool) (hs : s≠q) :
    D.CutInheritedSeamRowCoordinates q w s b hs := by
  change ((D.cutInheritedRows q w s b).trans
    ((C).portRowIndex ⟨.inl (D.ports.attach.symm (s,b)).1,(D.ports.attach.symm (s,b)).2⟩)).trans
    (finCongr (congrArg (C).seamDim (congrArg Prod.fst (D.cutInherited_attach q w s b hs))))=
    D.cutInheritedSeamRows q w s
  apply Equiv.ext
  intro i
  apply Fin.ext
  rfl

/-- Inherited seam columns retain the grades of their original child coordinates. -/
def CutInheritedSeamGrades : Prop :=
  ∀ i : (i : Fin (arity s)) × Fin (D.childDim s i),
    (C).seamGrade (D.cutOldSeam q w.shape s) (D.cutInheritedSeamColumns q w s i)=i.1.val

lemma cutInheritedSeamColumns_grade : D.CutInheritedSeamGrades q w s := by
  intro i
  change (C).seamGrade (D.cutOldSeam q w.shape s)
    (D.cutInheritedSeamColumns q w s i)=i.1.val
  exact (C).seamGrade_common (D.childDim s) (D.cutOldSeam q w.shape s)
    (finCongr (D.cutOldSeam_arity q w.shape s).symm)
    (fun j=>(D.cutOldSideRank q w.shape rfl w.rowRanks w.colRanks s (some j)).symm)
    (D.cutInheritedSeamColumns q w s) rfl (fun _=>rfl) i

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades HomTransport
variable {F S V K R : Type} {arity : S → ℕ} [Field K] [CommRing R]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (φ : R →+* K)
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) K)ˣ)
local notation "C" => D.refinedMarkedDiagram q w.shape rfl w.rowRanks w.colRanks hproper hmax
local notation "FF" => D.markedCutFrames q w hproper hmax (D.portFrame g) T
local notation "gg" => valuesFromPorts (C) (FF)
  (D.refinedCutSideValues q w.shape rfl w.rowRanks w.colRanks
    (fun a=>g (Generator.side a)) J Y)

/-- A framed flag equation on an uncut seam is retained in the marked cut diagram. -/
def MarkedInheritedSeamFlags : Prop :=
  ∀ (handle : (C).HandleValues (R:=K)) (s : S), s≠q →
    SameFramedFlag (fun i : (i : Fin (arity s)) × Fin (D.childDim s i) => i.1.val)
      ((D.namedSeamFrame s (g (.frame s false))).trans (D.namedParentLinear s g))
      ((D.namedChildInverse s g).trans (D.namedSeamFrame s (g (.frame s true)))) →
    SameFramedFlag ((C).seamGrade (D.cutOldSeam q w.shape s))
      (matrixUnitEquiv (((C).seamLeft (D.cutOldSeam q w.shape s)).eval φ ((gg) handle)))
      (matrixUnitEquiv (((C).seamRight (D.cutOldSeam q w.shape s)).eval φ ((gg) handle)))

lemma markedInherited_seamHolds :
    D.MarkedInheritedSeamFlags q g w T hproper hmax φ J Y := by
  intro handle s hs hold
  change SameFramedFlag ((C).seamGrade (D.cutOldSeam q w.shape s))
    (matrixUnitEquiv (((C).seamLeft (D.cutOldSeam q w.shape s)).eval φ ((gg) handle)))
    (matrixUnitEquiv (((C).seamRight (D.cutOldSeam q w.shape s)).eval φ ((gg) handle)))
  have hf (b : Bool) :
      ((MatrixIso.unit (((gg) handle) (.frame (D.cutOldSeam q w.shape s) b))).reindex
        (D.cutInheritedSeamColumns q w s) (D.cutInheritedSeamRows q w s)).linearEquiv=
        D.namedSeamFrame s (g (.frame s b)) := by
    exact ((C).frameValues_coordinates (FF)
      ⟨.inl (D.ports.attach.symm (s,b)).1,(D.ports.attach.symm (s,b)).2⟩
      (D.cutOldSeam q w.shape s) b (D.cutInherited_attach q w s b hs)
      (D.cutInheritedColumns q w s b) (D.cutInheritedRows q w s b)
      (D.cutInheritedSeamColumns q w s) (D.cutInheritedSeamRows q w s)
      (D.cutInheritedSeamColumns_coordinates q w s b hs)
      (D.cutInheritedSeamRows_coordinates q w s b hs)).trans
      (D.cutInherited_frameCoordinates q w s b g T)
  apply (C).seamHolds_of_coordinates (D.cutOldSeam q w.shape s) φ ((gg) handle)
    (D.cutInheritedSeamColumns q w s) (D.cutInheritedSeamRows q w s)
    (fun i : (i : Fin (arity s)) × Fin (D.childDim s i) => i.1.val)
    (D.namedSeamFrame s (g (.frame s false))) (D.namedSeamFrame s (g (.frame s true)))
    (D.namedParentLinear s g) (D.namedChildInverse s g)
  · exact D.cutInheritedSeamColumns_grade q w s
  · exact hf false
  · exact hf true
  · exact (C).parentWord_coordinates (D.cutOldSeam q w.shape s) φ ((gg) handle)
      (D.cutOldSideRank q w.shape rfl w.rowRanks w.colRanks s none) (g (.side ⟨s,none⟩))
      (D.refinedCutSideValues_unchanged_parent q w.shape rfl w.rowRanks w.colRanks
        (fun a=>g (.side a)) J Y s hs)
      (D.cutInheritedSeamRows q w s) rfl
  · exact (C).childWord_coordinates (D.cutOldSeam q w.shape s) φ ((gg) handle) (D.childDim s)
      (finCongr (D.cutOldSeam_arity q w.shape s).symm)
      (fun i=>(D.cutOldSideRank q w.shape rfl w.rowRanks w.colRanks s (some i)).symm)
      (fun i=>g (.side ⟨s,some i⟩))
      (fun i=>D.refinedCutSideValues_old_child q w.shape rfl w.rowRanks w.colRanks
        (fun a=>g (.side a)) J Y s i)
      (D.cutInheritedSeamColumns q w s) rfl
  · exact hold
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
