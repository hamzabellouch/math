import OAI.AlgebraicGeometry.CharacterVarieties.Frames.ShortCoordinates
import OAI.AlgebraicGeometry.CharacterVarieties.Frames.FrameTransport

namespace OAI



noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable MatrixExpression
variable {F S V K : Type} {arity : S → ℕ} [Field K]
    (D : Diagram F S V arity)
    {α β : Type*} [Fintype α] [Fintype β]
lemma frameValues_coordinates (F : D.PortFrames (R:=K))
    (p : LocalPort V D.ports.kind) (s : S) (b : Bool)
    (hp : D.ports.attach p=(s,b))
    (e : α ≃ (D.vertexRanks p.1).Columns p.2)
    (f : β ≃ (D.vertexRanks p.1).Parent p.2)
    (es : α ≃ Fin (D.seamDim s)) (fs : β ≃ Fin (D.seamDim s))
    (he : (e.trans (D.portColumnIndex p)).trans
      (finCongr (congrArg D.seamDim (congrArg Prod.fst hp)))=es)
    (hf : (f.trans (D.portRowIndex p)).trans
      (finCongr (congrArg D.seamDim (congrArg Prod.fst hp)))=fs) :
    ((MatrixIso.unit (D.frameValues F s b)).reindex es fs).linearEquiv=
      ((F p).reindex e f).linearEquiv := by
  have hs : (D.ports.attach p).1=s := congrArg Prod.fst hp
  have hb : (D.ports.attach p).2=b := congrArg Prod.snd hp
  subst s
  subst b
  simp only [finCongr_refl, Equiv.trans_refl] at he hf
  rw [←he, ←hf, D.frameValues_attach]
  simp only [localFrameUnit, MatrixIso.unit_toUnit, MatrixIso.reindex_reindex_eq,
    Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl]

omit [Fintype α] in
/-- Matching local coordinates agree as seam matrix coordinates. -/
lemma common_portColumnIndex
    (p u : LocalPort V D.ports.kind) (s : S) (b c : Bool)
    (hp : D.ports.attach p=(s,b)) (hu : D.ports.attach u=(s,c))
    (h : (D.ports.attach p).1=(D.ports.attach u).1)
    (e : α ≃ (D.vertexRanks p.1).Columns p.2)
    (eu : α ≃ (D.vertexRanks u.1).Columns u.2)
    (hm : e.trans (D.portColumnMatch p u h)=eu) :
    (eu.trans (D.portColumnIndex u)).trans
      (finCongr (congrArg D.seamDim (congrArg Prod.fst hu)))=
    (e.trans (D.portColumnIndex p)).trans
      (finCongr (congrArg D.seamDim (congrArg Prod.fst hp))) := by
  rw [←hm, Equiv.trans_assoc e, D.portColumnMatch_index]
  apply Equiv.ext
  intro i
  apply Fin.ext
  rfl
omit [Fintype β] in
lemma common_portRowIndex
    (p u : LocalPort V D.ports.kind) (s : S) (b c : Bool)
    (hp : D.ports.attach p=(s,b)) (hu : D.ports.attach u=(s,c))
    (h : (D.ports.attach p).1=(D.ports.attach u).1)
    (f : β ≃ (D.vertexRanks p.1).Parent p.2)
    (fu : β ≃ (D.vertexRanks u.1).Parent u.2)
    (hm : f.trans (D.portParentMatch p u h)=fu) :
    (fu.trans (D.portRowIndex u)).trans
      (finCongr (congrArg D.seamDim (congrArg Prod.fst hu)))=
    (f.trans (D.portRowIndex p)).trans
      (finCongr (congrArg D.seamDim (congrArg Prod.fst hp))) := by
  rw [←hm, Equiv.trans_assoc f, D.portParentMatch_index]
  apply Equiv.ext
  intro i
  apply Fin.ext
  rfl

/-- Child and within-child coordinate identities determine the ordered block-index equivalence. -/
lemma port_coordinates_blockIndex {m : ℕ} (d : Fin m → ℕ)
    (p : LocalPort V D.ports.kind) (s : S) (b : Bool)
    (hp : D.ports.attach p=(s,b))
    (c : Fin m ≃ Fin (arity s))
    (hc : ∀ i,d i=D.childDim s (c i))
    (e : ((i : Fin m) × Fin (d i)) ≃ (D.vertexRanks p.1).Columns p.2)
    (hi : ∀ i,((D.ports.kind p.1).childEnumeration p.2 (e i).1).val=(c i.1).val)
    (hj : ∀ i,(e i).2.val=i.2.val) :
    (e.trans (D.portColumnIndex p)).trans
      (finCongr (congrArg D.seamDim (congrArg Prod.fst hp)))=
      (Equiv.sigmaCongr c (fun i=>finCongr (hc i))).trans
        (blockIndex (D.childDim s)).symm := by
  have hs : (D.ports.attach p).1=s := congrArg Prod.fst hp
  subst s
  simp only [finCongr_refl,Equiv.trans_refl]
  apply Equiv.ext
  intro i
  apply (blockIndex (D.childDim (D.ports.attach p).1)).injective
  change (blockIndex _) ((blockIndex _).symm _)=(blockIndex _) ((blockIndex _).symm _)
  erw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  apply sigmaFin_ext_val _ _
  · apply Fin.ext
    exact hi i
  · exact hj i

lemma seamGrade_common {m : ℕ} (d : Fin m → ℕ) (s : S)
    (c : Fin m ≃ Fin (arity s)) (hc : ∀ i,d i=D.childDim s (c i))
    (e : ((i : Fin m) × Fin (d i)) ≃ Fin (D.seamDim s))
    (he : e=(Equiv.sigmaCongr c (fun i=>finCongr (hc i))).trans
      (blockIndex (D.childDim s)).symm)
    (hi : ∀ i,(c i).val=i.val) (i : (i : Fin m) × Fin (d i)) :
    D.seamGrade s (e i)=i.1.val := by
  rw [he]
  change ((blockIndex _) ((blockIndex _).symm _)).1.val=i.1.val
  rw [Equiv.apply_symm_apply]
  exact hi i.1

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
/-- The old positive port in the refined cut diagram. -/
def cutLastOldPort :
    LocalPort (V ⊕ (Fin (w.shape.atomicBand.length+1) ⊕ Fin (w.shape.atomicBand.length+1)))
      (C).ports.kind :=
  ⟨.inl (oo).1,(oo).2⟩
local notation "po" => D.cutLastOldPort q w
local notation "s" => D.cutOldSeam q w.shape q

def cutLastColumns : ((i : Fin (arity q)) × Fin (D.childDim q i)) ≃ Fin ((C).seamDim (s)) :=
  ((D.cutLastOldActualColumns q w).trans ((C).portColumnIndex (po))).trans
    (finCongr (congrArg (C).seamDim (congrArg Prod.fst (D.lastOldPositive_attach q w))))
def cutLastRows : Fin (D.rank (D.ports.facet ⟨q,none⟩)) ≃ Fin ((C).seamDim (s)) :=
  ((D.cutLastOldActualRows q w).trans ((C).portRowIndex (po))).trans
    (finCongr (congrArg (C).seamDim (congrArg Prod.fst (D.lastOldPositive_attach q w))))

lemma cutLastColumns_block :
    D.cutLastColumns q w=(Equiv.sigmaCongr
      (finCongr (D.cutOldSeam_arity q w.shape q).symm)
      (fun i=>finCongr (D.cutOldSideRank q w.shape rfl w.rowRanks w.colRanks q (some i)).symm)).trans
      (blockIndex ((C).childDim (s))).symm := by
  convert! (C).port_coordinates_blockIndex (D.childDim q) (po) (s) true
    (D.lastOldPositive_attach q w)
    (finCongr (D.cutOldSeam_arity q w.shape q).symm)
    (fun i=>(D.cutOldSideRank q w.shape rfl w.rowRanks w.colRanks q (some i)).symm)
    (D.cutLastOldActualColumns q w) ?_ ?_ using 1
  · intro i
    have hi := D.cutLast_grade q w i
    change (C).seamGrade ((C).ports.attach (po)).1
      ((C).portColumnIndex (po) (D.cutLastOldActualColumns q w i))=i.1.val at hi
    erw [(C).seamGrade_portColumnIndex] at hi
    convert! hi using 1
  · intro i
    change ((D.cutLastOldColumns q) i).2.val=i.2.val
    have h0 := congrArg Prod.fst (D.ports.attach.apply_symm_apply (q,true))
    exact (sigmaFinRefl_symm_val (m := D.childDim (D.ports.attach (oo)).1)
      (D.ports.childEquiv (oo)) _).trans
      (sigmaFinCongr_symm_val (m := D.childDim q)
        (finCongr (congrArg arity h0))
        (fun j=>congrArg (fun a=>D.rank (D.ports.facet a)) (side_child_congr h0 j)) i)

lemma cutLastRows_finCongr : D.cutLastRows q w=
    finCongr ((D.cutOldSideRank q w.shape rfl w.rowRanks w.colRanks q none).symm.trans
      ((C).seamRank (s))) := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  rfl

lemma cutLastColumns_grade (i : (i : Fin (arity q)) × Fin (D.childDim q i)) :
    (C).seamGrade (s) (D.cutLastColumns q w i)=i.1.val := by
  apply (C).seamGrade_common (D.childDim q) (s)
    (finCongr (D.cutOldSeam_arity q w.shape q).symm)
    (fun j=>(D.cutOldSideRank q w.shape rfl w.rowRanks w.colRanks q (some j)).symm)
    (D.cutLastColumns q w) (D.cutLastColumns_block q w) (fun _=>rfl)

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
