import Mathlib
import OAI.Computability.VertexCover.Machines.RegularRow
import OAI.Computability.VertexCover.Machines.PortBuilder

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine.OverlayMachine
open UniqueGames.Foundations.PCP
open TableMachine PreprocessingOverlayTables

abbrev Input (d e : ℕ) := Σ n, PortTables.Table n d × ExpanderTables.Table n e
def base {d e : ℕ} (T : Input d e) : PortTables.Input d := ⟨T.1,T.2.1⟩
def rows {d e : ℕ} (T : Input d e) : List ℕ := T.2.2.rows.toList.map Fin.val
def code {d e : ℕ} (T : Input d e) := prodBits PortMachine.code (listBits natBits) (base T,rows T)
def output {d e : ℕ} (T : Input d e) : PortTables.Input (d+e) := ⟨T.1,overlay T.2.1 T.2.2⟩

noncomputable def basePoly {d e : ℕ} : Poly (code (d := d) (e := e)) PortMachine.code base :=
  (Poly.fst PortMachine.code (listBits natBits)).encodeCongr (fun T => (base T,rows T))
    (fun _ => rfl) (fun _ => rfl)
noncomputable def rowsPoly {d e : ℕ} : Poly (code (d := d) (e := e)) (listBits natBits) rows :=
  (Poly.snd PortMachine.code (listBits natBits)).encodeCongr (fun T => (base T,rows T))
    (fun _ => rfl) (fun _ => rfl)

def pairReverse {d e : ℕ} (x : Input d e × (ℕ × ℕ)) : ℕ × ℕ :=
  if x.2.2 < d then
    ExpandMachine.lookup d ((x.1.2.1.reverseIndex.toList.map Fin.val),x.2)
  else
    let r := ExpandMachine.lookup e (rows x.1,(x.2.1,x.2.2-d))
    (r.1,d+r.2)
def reverse {d e : ℕ} (x : Input d e × ℕ) : ℕ :=
  let r := pairReverse (x.1,(x.2/(d+e),x.2%(d+e)))
  r.2+(d+e)*r.1
def relation {d e : ℕ} (x : Input d e × ℕ) : GraphTables.RelationTable :=
  if x.2%(d+e) < d then
    x.1.2.1.relations.toList.getD (x.2%(d+e)+d*(x.2/(d+e))) relationDefault
  else RegularMachine.trueRelation

noncomputable def pairReversePoly {d e : ℕ} :
    Poly (prodBits (code (d := d) (e := e)) (prodBits natBits natBits))
      (prodBits natBits natBits) pairReverse := by
  let en := prodBits natBits natBits
  let ec := code (d := d) (e := e)
  let t := Poly.fst ec en
  let x := Poly.snd ec en
  let v := x.comp (Poly.fst natBits natBits)
  let p := x.comp (Poly.snd natBits natBits)
  let c := Poly.const (prodBits ec en) natBits d
  let test := (p.pair c).comp Poly.natLt
  let old := ((t.comp (basePoly.comp PortMachine.reverseListPoly)).pair x).comp (ExpandMachine.lookupPoly d)
  let new := ((t.comp rowsPoly).pair (v.pair ((p.pair c).comp Poly.natSub))).comp (ExpandMachine.lookupPoly e)
  let out := (new.comp (Poly.fst natBits natBits)).pair
    ((c.pair (new.comp (Poly.snd natBits natBits))).comp Poly.natAdd)
  exact (test.ite old out).congr (fun _ => by simp only [Function.comp_apply,pairReverse,base,decide_eq_true_eq])

noncomputable def reversePoly {d e : ℕ} : Poly (prodBits (code (d := d) (e := e)) natBits) natBits reverse := by
  let ec := code (d := d) (e := e)
  let t := Poly.fst ec natBits
  let i := Poly.snd ec natBits
  let c := Poly.const (prodBits ec natBits) natBits (d+e)
  let x := ((i.pair c).comp Poly.natDiv).pair ((i.pair c).comp Poly.natMod)
  let r := (t.pair x).comp pairReversePoly
  exact ((r.comp (Poly.snd natBits natBits)).pair
    ((c.pair (r.comp (Poly.fst natBits natBits))).comp Poly.natMul)).comp Poly.natAdd

noncomputable def relationPoly {d e : ℕ} : Poly (prodBits (code (d := d) (e := e)) natBits) relationCode relation := by
  let ec := code (d := d) (e := e)
  let t := (Poly.fst ec natBits).comp basePoly
  let i := Poly.snd ec natBits
  let c := Poly.const (prodBits ec natBits) natBits (d+e)
  let cd := Poly.const (prodBits ec natBits) natBits d
  let v := (i.pair c).comp Poly.natDiv
  let p := (i.pair c).comp Poly.natMod
  let idx := (p.pair ((cd.pair v).comp Poly.natMul)).comp Poly.natAdd
  exact (((p.pair cd).comp Poly.natLt).ite ((t.pair idx).comp PortMachine.relationPoly)
    (Poly.const _ relationCode RegularMachine.trueRelation)).congr (fun _ => by
      simp only [Function.comp_apply,relation,base,decide_eq_true_eq])

 theorem lookup_port {n d : ℕ} (T : PortTables.Table n d) (x : Fin n × Fin d) :
    ExpandMachine.lookup d (T.reverseIndex.toList.map Fin.val,(x.1.val,x.2.val)) =
      ((PortTables.rotation T x).1.val,(PortTables.rotation T x).2.val) := by
  dsimp only [ExpandMachine.lookup]
  have hidx : x.2.val+d*x.1.val < (T.reverseIndex.toList.map Fin.val).length := by
    simpa using (PortTables.rowIndex n d x).isLt
  rw [List.getD_eq_getElem _ _ hidx,List.getElem_map]
  rfl

 theorem pairReverse_source {d e : ℕ} (T : Input d e) (v : Fin T.1) (p : Fin d ⊕ Fin e) :
    pairReverse (T,(v.val,(overlayPorts d e p).val)) =
      ((PortTables.rotation (output T).2 (v,overlayPorts d e p)).1.val,
       (PortTables.rotation (output T).2 (v,overlayPorts d e p)).2.val) := by
  change _ = ((PortTables.rotation (overlay T.2.1 T.2.2) (v,overlayPorts d e p)).1.val,
    (PortTables.rotation (overlay T.2.1 T.2.2) (v,overlayPorts d e p)).2.val)
  cases p with
  | inl p =>
    dsimp only [pairReverse]
    rw [overlayPorts_inl_val,ite_eq_left p.isLt]
    rw [lookup_port T.2.1 (v,p)]
    rw [overlay_rotation_old]
    rfl
  | inr p =>
    dsimp only [pairReverse,rows]
    rw [overlayPorts_inr_val,ite_eq_right (by omega),Nat.add_sub_cancel_left]
    rw [ExpandMachine.lookup_erase T.2.2 (v,p)]
    rw [overlay_rotation_expander]
    rfl

 theorem reverse_source {d e : ℕ} (T : Input d e) (i : Fin ((output T).1*(d+e))) :
    reverse (T,i.val) = (output T).2.reverseIndex[i].val := by
  let E := (Equiv.prodCongr (Equiv.refl (Fin T.1)) (overlayPorts d e)).trans (PortTables.rowIndex _ _)
  obtain ⟨⟨v,p⟩,rfl⟩ := E.surjective i
  have hi : ((E (v,p)).val/(d+e),(E (v,p)).val%(d+e)) = (v.val,(overlayPorts d e p).val) :=
    congrArg (fun z : Fin T.1 × Fin (d+e) => (z.1.val,z.2.val))
      ((PortTables.rowIndex _ _).symm_apply_apply (v,overlayPorts d e p))
  dsimp only [reverse]
  rw [hi,pairReverse_source]
  exact congrArg Fin.val (PortTables.rowIndex_rotation (output T).2 (v,overlayPorts d e p))

 theorem relation_source {d e : ℕ} (T : Input d e) (i : Fin ((output T).1*(d+e))) :
    relation (T,i.val) = (output T).2.relations[i] := by
  let E := (Equiv.prodCongr (Equiv.refl (Fin T.1)) (overlayPorts d e)).trans (PortTables.rowIndex _ _)
  obtain ⟨⟨v,p⟩,rfl⟩ := E.surjective i
  have hi : ((E (v,p)).val/(d+e),(E (v,p)).val%(d+e)) = (v.val,(overlayPorts d e p).val) :=
    congrArg (fun z : Fin T.1 × Fin (d+e) => (z.1.val,z.2.val))
      ((PortTables.rowIndex _ _).symm_apply_apply (v,overlayPorts d e p))
  change _ = (overlay T.2.1 T.2.2).relations[PortTables.rowIndex _ _ (v,overlayPorts d e p)]
  dsimp only [relation]
  have hv : (E (v,p)).val/(d+e) = v.val := congrArg Prod.fst hi
  have hp : (E (v,p)).val%(d+e) = (overlayPorts d e p).val := congrArg Prod.snd hi
  conv_lhs => rw [hv,hp]
  have extensionality {left right : GraphTables.RelationTable}
      (equal : ∀ first second,
        GraphTables.relationAt left first second = GraphTables.relationAt right first second) :
      left = right := by
    apply Vector.ext
    intro index index_lt
    simpa only [GraphTables.relationAt,Prod.eta,Equiv.apply_symm_apply,Fin.getElem_fin] using
      equal (GraphTables.relationIndex.symm ⟨index,index_lt⟩).1
        (GraphTables.relationIndex.symm ⟨index,index_lt⟩).2
  apply extensionality
  intro first second
  cases p with
  | inl p =>
    rw [overlayPorts_inl_val,ite_eq_left p.isLt,
      List.getD_eq_getElem _ _ (by simpa using (PortTables.rowIndex T.1 d (v,p)).isLt)]
    exact (overlay_accepts_old T.2.1 T.2.2 v p first second).symm
  | inr p =>
    rw [overlayPorts_inr_val,ite_eq_right (by omega),RegularMachine.trueRelation,GraphTables.relationAt_relationOf]
    exact (overlay_accepts_expander T.2.1 T.2.2 v p first second).symm

noncomputable def poly {d e : ℕ} : Poly (code (d := d) (e := e)) PortMachine.code output := by
  let zero : Input d e := ⟨0,
    PortTables.ofPortGraph {rot := Equiv.refl _,rot_involutive := fun _ => rfl}
      (fun _ _ _ => true) (fun _ _ _ => rfl),
    ExpanderTables.ofGraph {rot := Equiv.refl _,rot_involutive := fun _ => rfl}⟩
  exact PortMachine.materializePoly code zero output (basePoly.comp PortMachine.verticesPoly)
    reversePoly relationPoly reverse_source relation_source

end VertexCover.Machine.OverlayMachine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
