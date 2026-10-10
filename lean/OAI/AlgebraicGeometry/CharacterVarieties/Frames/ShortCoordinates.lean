import OAI.AlgebraicGeometry.CharacterVarieties.Frames.PortCoordinates

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades
lemma sigmaFin_ext_val {I : Type} {n : I → ℕ}
    (a b : (i : I) × Fin (n i)) (h : a.1=b.1) (hv : a.2.val=b.2.val) : a=b := by
  apply Sigma.ext h
  exact (Fin.heq_ext_iff (congrArg n h)).mpr hv
lemma sigmaFinCongr_val {I J : Type} {n : I → ℕ} {m : J → ℕ}
    (e : I ≃ J) (h : ∀ i,n i=m (e i)) (x : (i : I) × Fin (n i)) :
    ((Equiv.sigmaCongr (β₁ := fun i=>Fin (n i)) (β₂ := fun j=>Fin (m j)) e (fun i=>finCongr (h i))) x).2.val=x.2.val := rfl
lemma sigmaFinCongr_symm_val {I J : Type} {n : I → ℕ} {m : J → ℕ}
    (e : I ≃ J) (h : ∀ i,n i=m (e i)) (x : (j : J) × Fin (m j)) :
    ((Equiv.sigmaCongr (β₁ := fun i=>Fin (n i)) (β₂ := fun j=>Fin (m j)) e (fun i=>finCongr (h i))).symm x).2.val=x.2.val := by
  let E := Equiv.sigmaCongr (β₁ := fun i=>Fin (n i)) (β₂ := fun j=>Fin (m j)) e (fun i=>finCongr (h i))
  exact (sigmaFinCongr_val e h (E.symm x)).symm.trans
    (congrArg (fun z : (j : J) × Fin (m j)=>z.2.val) (E.apply_symm_apply x))
lemma sigmaFinRefl_symm_val {I J : Type} {m : J → ℕ}
    (e : I ≃ J) (x : (j : J) × Fin (m j)) :
    ((Equiv.sigmaCongr (β₂ := fun j=>Fin (m j)) e
      (fun i=>Equiv.refl (Fin (m (e i))))).symm x).2.val=x.2.val :=
  sigmaFinCongr_symm_val e (fun _=>rfl) x

private lemma transportFrames_frameCoordinates
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
local notation "oo" => D.ports.attach.symm (q,false)
local notation "h0" => congrArg Prod.fst (D.ports.attach.apply_symm_apply (q,false))
def cutFirstOldColumns : ((i : Fin (arity q)) × Fin (D.childDim q i)) ≃
    (D.vertexRanks (oo).1).Columns (oo).2 :=
  (D.namedColumnsMatch (h0)).symm.trans (D.portNamedColumns (oo))
def cutFirstOldRows : Fin (D.rank (D.ports.facet ⟨q,none⟩)) ≃
    (D.vertexRanks (oo).1).Parent (oo).2 :=
  finCongr (congrArg (fun z=>D.rank (D.ports.facet ⟨z,none⟩)) (h0)).symm
local notation "ho" => Eq.symm (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (Sigma.fst (D.ports.attach.symm (q,false))))
local notation "hn" => D.namedCut_orig_localRanks q w 0
local notation "pp" => Kind.input (w.shape.atomicBand.kind 0)
def cutFirstOldActualColumns := (D.cutFirstOldColumns q).trans (LocalRanks.columnCongr (ho) (oo).2)
def cutFirstOldActualRows := (D.cutFirstOldRows q).trans (LocalRanks.parentCongr (ho) (oo).2)
def cutFirstNewActualColumns := w.firstColumns.symm.trans (LocalRanks.columnCongr (hn) (pp))
def cutFirstNewActualRows := (finCongr w.firstParent_rank).symm.trans (LocalRanks.parentCongr (hn) (pp))
/-- Column coordinates at two ports are compatible with transport across the cut seam. -/
def CutColumnCoordinatesAligned {I : Type}
    (p u : LocalPort _ (C).ports.kind) (h : D.CutPortsAdjacent q w p u)
    (e : I ≃ ((C).vertexRanks p.1).Columns p.2)
    (eu : I ≃ ((C).vertexRanks u.1).Columns u.2) : Prop :=
  e.trans ((C).portColumnMatch p u h)=eu

/-- Compatibility of column coordinates at the negative endpoint of the cut band. -/
def FirstCutColumnsCompatible : Prop :=
  D.CutColumnCoordinatesAligned q w
    ⟨.inl (oo).1,(oo).2⟩ ⟨.inr (.inl 0),(pp)⟩ (D.firstAdjacentSame q w)
    (D.cutFirstOldActualColumns q w) (D.cutFirstNewActualColumns q w)

lemma cutFirstColumn_match : D.FirstCutColumnsCompatible q w := by
  change (D.cutFirstOldActualColumns q w).trans
    ((C).portColumnMatch ⟨.inl (oo).1,(oo).2⟩ ⟨.inr (.inl 0),(pp)⟩
      (D.firstAdjacentSame q w))=D.cutFirstNewActualColumns q w
  apply Equiv.ext
  intro i
  have hc : (((D.cutFirstOldActualColumns q w).trans
      ((C).portColumnMatch ⟨.inl (oo).1,(oo).2⟩ ⟨.inr (.inl 0),(pp)⟩
        (D.firstAdjacentSame q w))) i).1=(D.cutFirstNewActualColumns q w i).1 := by
    change (C).portChildMatch _ _ (D.firstAdjacentSame q w) _=_
    have hm := Equiv.congr_fun (D.firstChildMatch q w)
      ((D.cutFirstOldActualColumns q w i).1)
    apply hm.trans
    change w.firstChild.symm ((finCongr (congrArg arity (h0)))
      ((D.ports.childEquiv (oo)) ((D.ports.childEquiv (oo)).symm
        ((finCongr (congrArg arity (h0))).symm i.1))))=w.firstChild.symm i.1
    exact congrArg w.firstChild.symm
      ((congrArg (finCongr (congrArg arity (h0)))
        ((D.ports.childEquiv (oo)).apply_symm_apply
          ((finCongr (congrArg arity (h0))).symm i.1))).trans
        ((finCongr (congrArg arity (h0))).apply_symm_apply i.1))
  apply sigmaFin_ext_val _ _ hc
  change ((D.cutFirstOldColumns q) i).2.val=(w.firstColumns.symm i).2.val
  have h1 : ((D.namedColumnsMatch (h0)).symm i).2.val=i.2.val := by
    exact sigmaFinCongr_symm_val (m := D.childDim q)
      (finCongr (congrArg arity (h0)))
      (fun j=>congrArg (fun a=>D.rank (D.ports.facet a)) (side_child_congr (h0) j)) i
  have h2 : (D.portNamedColumns (oo) ((D.namedColumnsMatch (h0)).symm i)).2.val=
      ((D.namedColumnsMatch (h0)).symm i).2.val := by
    exact sigmaFinRefl_symm_val (m := D.childDim (D.ports.attach (oo)).1)
      (D.ports.childEquiv (oo)) _
  have h3 : (w.firstColumns.symm i).2.val=i.2.val := by
    exact sigmaFinCongr_symm_val (m := D.childDim q) w.firstChild w.firstChild_rank i
  exact h2.trans (h1.trans h3.symm)
/-- Compatibility of row coordinates at the negative endpoint of the cut band. -/
def FirstCutRowsCompatible : Prop :=
    (D.cutFirstOldActualRows q w).trans
      ((C).portParentMatch ⟨.inl (oo).1,(oo).2⟩ ⟨.inr (.inl 0),(pp)⟩
        (D.firstAdjacentSame q w))=D.cutFirstNewActualRows q w

lemma cutFirstRow_match : D.FirstCutRowsCompatible q w := by
  change (D.cutFirstOldActualRows q w).trans
    ((C).portParentMatch ⟨.inl (oo).1,(oo).2⟩ ⟨.inr (.inl 0),(pp)⟩
      (D.firstAdjacentSame q w))=D.cutFirstNewActualRows q w
  apply Equiv.ext
  intro i
  apply Fin.ext
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
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "oo" => D.ports.attach.symm (q,true)
lemma lastAdjacentSame :
    D.CutPortsAdjacent q w ⟨.inl (oo).1,(oo).2⟩
      ⟨.inr (.inl (Fin.last w.shape.atomicBand.length)),
        (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output⟩ := by
  change ((C).ports.attach ⟨.inl (oo).1,(oo).2⟩).1=_
  exact (congrArg Prod.fst (D.lastOldPositive_attach q w)).trans
    (congrArg Prod.fst (D.lastOriginalOutput_attach q w)).symm

def cutLastChild : (D.ports.kind (oo).1).table.Child (oo).2 ≃
    (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).table.Child (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output :=
  ((D.ports.childEquiv (oo)).trans
    (finCongr (congrArg arity (congrArg Prod.fst (D.ports.attach.apply_symm_apply (q,true)))))).trans
      w.lastChild.symm

omit [Finite V] in
lemma cutLastChild_enumeration (c : (D.ports.kind (oo).1).table.Child (oo).2) :
    (((w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).childEnumeration (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output)
      (D.cutLastChild q w c)).val=
      (((D.ports.kind (oo).1).childEnumeration (oo).2) c).val := by
  unfold cutLastChild IdentifiedBand.lastChild PortAssembly.childEquiv
  simp only [Equiv.trans_apply,Equiv.symm_trans_apply,Equiv.apply_symm_apply]
  rfl

/-- Child transport from the old positive end to the last vertex of the cut band. -/
def lastCutChildTransport :
    (D.ports.kind (oo).1).table.Child (oo).2 ≃
      (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).table.Child
        (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output :=
  (C).portChildMatch ⟨.inl (oo).1,(oo).2⟩
    ⟨.inr (.inl (Fin.last w.shape.atomicBand.length)),
      (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output⟩
    (D.lastAdjacentSame q w)

lemma lastChildMatch :
    D.lastCutChildTransport q w=D.cutLastChild q w := by
  change (C).portChildMatch ⟨.inl (oo).1,(oo).2⟩
    ⟨.inr (.inl (Fin.last w.shape.atomicBand.length)),
      (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length)).output⟩
    (D.lastAdjacentSame q w)=D.cutLastChild q w
  apply (C).portChildMatch_eq_of_enumeration
  exact D.cutLastChild_enumeration q w
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
local notation "oo" => D.ports.attach.symm (q,true)
local notation "h0" => congrArg Prod.fst (D.ports.attach.apply_symm_apply (q,true))
def cutLastOldColumns : ((i : Fin (arity q)) × Fin (D.childDim q i)) ≃
    (D.vertexRanks (oo).1).Columns (oo).2 :=
  (D.namedColumnsMatch (h0)).symm.trans (D.portNamedColumns (oo))
def cutLastOldRows : Fin (D.rank (D.ports.facet ⟨q,none⟩)) ≃
    (D.vertexRanks (oo).1).Parent (oo).2 :=
  finCongr (congrArg (fun z=>D.rank (D.ports.facet ⟨z,none⟩)) (h0)).symm
local notation "ho" => Eq.symm (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (Sigma.fst (D.ports.attach.symm (q,true))))
local notation "hn" => D.namedCut_orig_localRanks q w (Fin.last w.shape.atomicBand.length)
local notation "pp" => Kind.output (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length))
def cutLastOldActualColumns := (D.cutLastOldColumns q).trans (LocalRanks.columnCongr (ho) (oo).2)
def cutLastOldActualRows := (D.cutLastOldRows q).trans (LocalRanks.parentCongr (ho) (oo).2)
def cutLastNewActualColumns := w.lastColumns.symm.trans (LocalRanks.columnCongr (hn) (pp))
def cutLastNewActualRows := (finCongr w.lastParent_rank).symm.trans (LocalRanks.parentCongr (hn) (pp))
/-- Compatibility of column coordinates at the positive endpoint of the cut band. -/
def LastCutColumnsCompatible : Prop :=
  D.CutColumnCoordinatesAligned q w
    ⟨.inl (oo).1,(oo).2⟩ ⟨.inr (.inl (Fin.last w.shape.atomicBand.length)),(pp)⟩
    (D.lastAdjacentSame q w)
    (D.cutLastOldActualColumns q w) (D.cutLastNewActualColumns q w)

lemma cutLastColumn_match : D.LastCutColumnsCompatible q w := by
  change (D.cutLastOldActualColumns q w).trans
    ((C).portColumnMatch ⟨.inl (oo).1,(oo).2⟩
      ⟨.inr (.inl (Fin.last w.shape.atomicBand.length)),(pp)⟩
      (D.lastAdjacentSame q w))=D.cutLastNewActualColumns q w
  apply Equiv.ext
  intro i
  have hc : (((D.cutLastOldActualColumns q w).trans
      ((C).portColumnMatch ⟨.inl (oo).1,(oo).2⟩ ⟨.inr (.inl (Fin.last w.shape.atomicBand.length)),(pp)⟩
        (D.lastAdjacentSame q w))) i).1=(D.cutLastNewActualColumns q w i).1 := by
    change (C).portChildMatch _ _ (D.lastAdjacentSame q w) _=_
    have hm := Equiv.congr_fun (D.lastChildMatch q w)
      ((D.cutLastOldActualColumns q w i).1)
    apply hm.trans
    change w.lastChild.symm ((finCongr (congrArg arity (h0)))
      ((D.ports.childEquiv (oo)) ((D.ports.childEquiv (oo)).symm
        ((finCongr (congrArg arity (h0))).symm i.1))))=w.lastChild.symm i.1
    exact congrArg w.lastChild.symm
      ((congrArg (finCongr (congrArg arity (h0)))
        ((D.ports.childEquiv (oo)).apply_symm_apply
          ((finCongr (congrArg arity (h0))).symm i.1))).trans
        ((finCongr (congrArg arity (h0))).apply_symm_apply i.1))
  apply sigmaFin_ext_val _ _ hc
  change ((D.cutLastOldColumns q) i).2.val=(w.lastColumns.symm i).2.val
  have h1 : ((D.namedColumnsMatch (h0)).symm i).2.val=i.2.val := by
    exact sigmaFinCongr_symm_val (m := D.childDim q)
      (finCongr (congrArg arity (h0)))
      (fun j=>congrArg (fun a=>D.rank (D.ports.facet a)) (side_child_congr (h0) j)) i
  have h2 : (D.portNamedColumns (oo) ((D.namedColumnsMatch (h0)).symm i)).2.val=
      ((D.namedColumnsMatch (h0)).symm i).2.val := by
    exact sigmaFinRefl_symm_val (m := D.childDim (D.ports.attach (oo)).1)
      (D.ports.childEquiv (oo)) _
  have h3 : (w.lastColumns.symm i).2.val=i.2.val := by
    exact sigmaFinCongr_symm_val (m := D.childDim q) w.lastChild w.lastChild_rank i
  exact h2.trans (h1.trans h3.symm)
/-- Compatibility of row coordinates at the positive endpoint of the cut band. -/
def LastCutRowsCompatible : Prop :=
    (D.cutLastOldActualRows q w).trans
      ((C).portParentMatch ⟨.inl (oo).1,(oo).2⟩ ⟨.inr (.inl (Fin.last w.shape.atomicBand.length)),(pp)⟩
        (D.lastAdjacentSame q w))=D.cutLastNewActualRows q w

lemma cutLastRow_match : D.LastCutRowsCompatible q w := by
  change (D.cutLastOldActualRows q w).trans
    ((C).portParentMatch ⟨.inl (oo).1,(oo).2⟩ ⟨.inr (.inl (Fin.last w.shape.atomicBand.length)),(pp)⟩
      (D.lastAdjacentSame q w))=D.cutLastNewActualRows q w
  apply Equiv.ext
  intro i
  apply Fin.ext
  rfl
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression NamedBandGrades
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity) (q : S) [Finite V]
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    {f h : (((i : Fin (arity q)) × Fin (D.childDim q i)) → K) ≃ₗ[K]
      (Fin (D.rank (D.ports.facet ⟨q,none⟩)) → K)}
    (w : IdentifiedBand (D.childDim q) f h)
    (T : MatrixIso K (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))))
local notation "C" => D.refinedCutDiagram q w.shape rfl w.rowRanks w.colRanks
local notation "FF" => D.namedCutPortFrames q w (D.portFrame g) T
local notation "oo" => D.ports.attach.symm (q,true)
local notation "ho" => Eq.symm (D.refinedCut_old_vertexRanks q w.shape rfl w.rowRanks w.colRanks (Sigma.fst (D.ports.attach.symm (q,true))))
local notation "hn" => D.namedCut_orig_localRanks q w (Fin.last w.shape.atomicBand.length)
local notation "pp" => Kind.output (w.shape.atomicBand.kind (Fin.last w.shape.atomicBand.length))
/-- The old positive frame retains its named seam coordinates after the cut. -/
def LastCutOldFrameCompatible : Prop :=
    (((FF) ⟨.inl (oo).1,(oo).2⟩).reindex
      (D.cutLastOldActualColumns q w) (D.cutLastOldActualRows q w)).linearEquiv=
      D.namedSeamFrame q (g (.frame q true))

/-- The new positive frame has the terminal coordinates of the identified band. -/
def LastCutNewFrameCompatible : Prop :=
    (((FF) ⟨.inr (.inl (Fin.last w.shape.atomicBand.length)),(pp)⟩).reindex
      (D.cutLastNewActualColumns q w) (D.cutLastNewActualRows q w)).linearEquiv=w.lastFrame

lemma cutLast_old_frameCoordinates : D.LastCutOldFrameCompatible q g w T := by
  change (((FF) ⟨.inl (oo).1,(oo).2⟩).reindex
    (D.cutLastOldActualColumns q w) (D.cutLastOldActualRows q w)).linearEquiv=
    D.namedSeamFrame q (g (.frame q true))
  exact (transportFrames_frameCoordinates (ho)
    (fun p => D.portFrame g ⟨(oo).1,p⟩) (oo).2
    (D.cutLastOldColumns q) (D.cutLastOldRows q)).trans
      (D.portFrame_namedCoordinates g (oo) q true
        (D.ports.attach.apply_symm_apply (q,true)))
lemma cutLast_new_frameCoordinates : D.LastCutNewFrameCompatible q g w T := by
  change (((FF) ⟨.inr (.inl (Fin.last w.shape.atomicBand.length)),(pp)⟩).reindex
    (D.cutLastNewActualColumns q w) (D.cutLastNewActualRows q w)).linearEquiv=w.lastFrame
  exact transportFrames_frameCoordinates (hn)
    (w.vertexFrames (Fin.last w.shape.atomicBand.length)) (pp)
    w.lastColumns.symm (finCongr w.lastParent_rank).symm
/-- A positive endpoint column has the grade of its original child coordinate. -/
def LastCutColumnHasGrade (i : (i : Fin (arity q)) × Fin (D.childDim q i)) : Prop :=
    (C).seamGrade ((C).ports.attach ⟨.inl (oo).1,(oo).2⟩).1
      ((C).portColumnIndex ⟨.inl (oo).1,(oo).2⟩ (D.cutLastOldActualColumns q w i))=i.1.val

lemma cutLast_grade (i : (i : Fin (arity q)) × Fin (D.childDim q i)) :
    D.LastCutColumnHasGrade q w i := by
  change (C).seamGrade ((C).ports.attach ⟨.inl (oo).1,(oo).2⟩).1
    ((C).portColumnIndex ⟨.inl (oo).1,(oo).2⟩ (D.cutLastOldActualColumns q w i))=i.1.val
  rw [(C).seamGrade_portColumnIndex]
  change (((D.ports.kind (oo).1).childEnumeration (oo).2)
    ((D.ports.childEquiv (oo)).symm ((finCongr (congrArg arity
      (congrArg Prod.fst (D.ports.attach.apply_symm_apply (q,true))))).symm i.1))).val=_
  simp only [PortAssembly.childEquiv,Equiv.symm_trans_apply,Equiv.apply_symm_apply]
  rfl
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable TwoFlagBand NamedBandGrades MatrixExpression
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {r : ℕ} (d : RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
local notation "C" => D.refinedCutDiagram q d hp hc hc'
local notation "B" => D.ports.refinedBandForSeam q d
local notation "A" => D.ports.mapFacet (Sum.inl : F → D.ports.RefinedBandFacet q d)
omit [Finite V] in
private lemma oldSignatureMatch :
    (B).doublePatch.SignatureMatch (doubleDecoration (B).decoration) :=
  (B).patch.double_signatureMatch (B).decoration (B).patch_signatureMatch (B).shortFirst (B).shortLast

omit [Finite V] in
private lemma oldPlusSignature :
    ∀ i,portSignature (doubleDecoration (B).decoration) ((B).doublePatch.plus (.inr i)).val=
      (A).seamSignature q := by
  intro i
  rw [(B).double_signature_plus]
  cases i <;> rfl

omit [Finite V] in
private lemma oldMinusSignature :
    ∀ i,portSignature (doubleDecoration (B).decoration) ((B).doublePatch.minus (.inr i)).val=
      (A).seamSignature q := by
  intro i
  rw [(B).double_signature_minus]
  cases i <;> rfl

local notation "hi" => oldSignatureMatch D q d
local notation "hp'" => oldPlusSignature D q d
local notation "hm'" => oldMinusSignature D q d

def cutOldSeam (s : S) := BandGraft.oldPort (A) q (B) s true
omit [Finite V] in
lemma cutOldSeam_arity (s : S) :
    (BandGraft.wiring (A) q (B)).seamArity (D.cutOldSeam q d s)=arity s :=
  graftLabelArity_old (A) (B).doublePatch (doubleDecoration (B).decoration) q (hi) (hp') (hm') s

lemma cutOldSideRank (s : S) (i : Option (Fin (arity s))) :
    (C).rank ((C).ports.facet ⟨D.cutOldSeam q d s,
      i.map (finCongr (D.cutOldSeam_arity q d s).symm)⟩)=D.rank (D.ports.facet ⟨s,i⟩) := by
  exact congrArg (D.ports.refinedRank q d D.rank)
    (graft_old_color (A) (B).doublePatch (doubleDecoration (B).decoration) q (hi) (hp') (hm') s i)

variable (old : D.SideValues (R:=R))
    (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) R)ˣ)
/-- Side values of the cut diagram expressed in the original seam ranks. -/
def refinedCutOldSideValues : D.SideValues (R:=R) :=
  fun a => rebaseUnit (D.cutOldSideRank q d hp hc hc' a.1 a.2)
    (D.refinedCutSideValues q d hp hc hc' old J Y
      ⟨D.cutOldSeam q d a.1,a.2.map (finCongr (D.cutOldSeam_arity q d a.1).symm)⟩)

lemma refinedCutSideValues_old (s : S) (i : Option (Fin (arity s))) :
    D.refinedCutOldSideValues q d hp hc hc' old J Y ⟨s,i⟩=
      D.cutOldSideValues q old J ⟨s,i⟩ := by
  exact graftSideValues_old (A) (B).doublePatch (doubleDecoration (B).decoration) q
    (hi) (hp') (hm') (D.ports.refinedRank q d D.rank)
    (D.cutOldSideValues q old J) (D.cutShortSideValues q Y) s i

lemma refinedCutSideValues_last_parent :
    D.refinedCutOldSideValues q d hp hc hc' old J Y ⟨q,none⟩=J := by
  exact (D.refinedCutSideValues_old q d hp hc hc' old J Y q none).trans
    (D.cutOldSideValues_selected q old J)

lemma refinedCutSideValues_old_child (s : S) (i : Fin (arity s)) :
    D.refinedCutOldSideValues q d hp hc hc' old J Y ⟨s,some i⟩=
      old ⟨s,some i⟩ :=
  D.refinedCutSideValues_old q d hp hc hc' old J Y s (some i)

lemma refinedCutSideValues_unchanged_parent (s : S) (hs : s≠q) :
    D.refinedCutOldSideValues q d hp hc hc' old J Y ⟨s,none⟩=
      old ⟨s,none⟩ := by
  refine (D.refinedCutSideValues_old q d hp hc hc' old J Y s none).trans ?_
  simp only [cutOldSideValues,dite_eq_right hs]

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
