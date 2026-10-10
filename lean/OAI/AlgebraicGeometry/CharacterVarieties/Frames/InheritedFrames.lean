import OAI.AlgebraicGeometry.CharacterVarieties.Frames.MarkedFrames
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.ShortCoordinates

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades
private lemma transportInheritedFrames_coordinates
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
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "B" => D.ports.refinedBandForSeam q w.shape
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q w.shape)
local notation "W" => BandGraft.wiring (A) q (B)
variable (s : S) (b : Bool)
local notation "oo" => D.ports.attach.symm (s,b)
local notation "ha" => D.ports.attach.apply_symm_apply (s,b)
local notation "h0" => congrArg Prod.fst (ha)
local notation "ht" => Eq.symm (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (Sigma.fst (oo)))

def cutInheritedColumns : ((i : Fin (arity s)) × Fin (D.childDim s i)) ≃
    ((C).vertexRanks (.inl (oo).1)).Columns (oo).2 :=
  (((D.namedColumnsMatch (h0)).symm.trans (D.portNamedColumns (oo))).trans
    (LocalRanks.columnCongr (ht) (oo).2))
def cutInheritedRows : Fin (D.rank (D.ports.facet ⟨s,none⟩)) ≃
    ((C).vertexRanks (.inl (oo).1)).Parent (oo).2 :=
  (finCongr (congrArg (fun z=>D.rank (D.ports.facet ⟨z,none⟩)) (h0))).symm.trans
    (LocalRanks.parentCongr (ht) (oo).2)

lemma cutInherited_attach (hs : s≠q) :
    D.CutPortAttached q w ⟨.inl (oo).1,(oo).2⟩ (D.cutOldSeam q w.shape s,b) := by
  change (C).ports.attach ⟨.inl (oo).1,(oo).2⟩=(D.cutOldSeam q w.shape s,b)
  cases b with
  | false =>
    have hh := (W).endOf_portAt (BandGraft.oldPort (A) q (B) s true,false)
    change (W).endOf ((W).wire (BandGraft.oldPort (A) q (B) s true)).val=_ at hh
    erw [BandGraft.wire_old _ _ _ s hs] at hh
    exact hh
  | true =>
    exact (W).endOf_portAt (BandGraft.oldPort (A) q (B) s true,true)

/-- Every inherited port frame agrees with the original frame in the original seam coordinates. -/
def CutInheritedFrameCoordinates : Prop :=
  ∀ (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)))),
    (((D.namedCutPortFrames q w (D.portFrame g) T) ⟨.inl (oo).1,(oo).2⟩).reindex
      (D.cutInheritedColumns q w s b) (D.cutInheritedRows q w s b)).linearEquiv=
      D.namedSeamFrame s (g (.frame s b))

lemma cutInherited_frameCoordinates :
    D.CutInheritedFrameCoordinates q w s b := by
  intro g T
  convert! (transportInheritedFrames_coordinates (ht)
    (fun p => D.portFrame g ⟨(oo).1,p⟩) (oo).2
    ((D.namedColumnsMatch (h0)).symm.trans (D.portNamedColumns (oo)))
    (finCongr (congrArg (fun z => D.rank (D.ports.facet ⟨z,none⟩)) (h0))).symm).trans
      (D.portFrame_namedCoordinates g (oo) s b (ha)) using 1

/-- The inherited column coordinates keep the original child label. -/
def CutInheritedChildLabels : Prop :=
  ∀ i : (i : Fin (arity s)) × Fin (D.childDim s i),
    (((C).ports.kind (.inl (oo).1)).childEnumeration (oo).2
      (D.cutInheritedColumns q w s b i).1).val=i.1.val

lemma cutInheritedColumns_childEnumeration :
    D.CutInheritedChildLabels q w s b := by
  intro i
  change (((D.ports.kind (oo).1).childEnumeration (oo).2)
    ((D.ports.childEquiv (oo)).symm ((finCongr (congrArg arity (h0))).symm i.1))).val=_
  simp only [PortAssembly.childEquiv,Equiv.symm_trans_apply,Equiv.apply_symm_apply]
  rfl

/-- The inherited column coordinates keep the position inside each child. -/
def CutInheritedColumnValues : Prop :=
  ∀ i : (i : Fin (arity s)) × Fin (D.childDim s i),
    (D.cutInheritedColumns q w s b i).2.val=i.2.val

lemma cutInheritedColumns_value :
    D.CutInheritedColumnValues q w s b := by
  intro i
  change (D.portNamedColumns (oo) ((D.namedColumnsMatch (h0)).symm i)).2.val=i.2.val
  exact (sigmaFinRefl_symm_val (m := D.childDim (D.ports.attach (oo)).1)
    (D.ports.childEquiv (oo)) _).trans
    (sigmaFinCongr_symm_val (m := D.childDim s)
      (finCongr (congrArg arity (h0)))
      (fun j=>congrArg (fun a=>D.rank (D.ports.facet a)) (side_child_congr (h0) j)) i)

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
