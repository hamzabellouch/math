import Mathlib
import OAI.Computability.VertexCover.Machines.Overlay

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

namespace VertexCover.Machine.LazyMachine
open UniqueGames.Foundations.PCP
open TableMachine PreprocessingOverlayTables

def output {d : ℕ} (T : PortTables.Input d) : PortTables.Input (2*d) := ⟨T.1,lazy T.2⟩

def reverse {d : ℕ} (x : PortTables.Input d × ℕ) : ℕ :=
  let v := x.2/(2*d)
  let p := x.2%(2*d)
  if p<d then x.2 else
    let r := ExpandMachine.lookup d (x.1.2.reverseIndex.toList.map Fin.val,(v,p-d))
    (r.2+d)+(2*d)*r.1

def relation {d : ℕ} (x : PortTables.Input d × ℕ) : GraphTables.RelationTable :=
  if x.2%(2*d)<d then RegularMachine.trueRelation else
    x.1.2.relations.toList.getD (x.2%(2*d)-d+d*(x.2/(2*d))) relationDefault

noncomputable def reversePoly {d : ℕ} : Poly (prodBits (PortMachine.code (q := d)) natBits) natBits reverse := by
  let ec := PortMachine.code (q := d)
  let t := Poly.fst ec natBits
  let i := Poly.snd ec natBits
  let c := Poly.const (prodBits ec natBits) natBits (2*d)
  let cd := Poly.const (prodBits ec natBits) natBits d
  let v := (i.pair c).comp Poly.natDiv
  let p := (i.pair c).comp Poly.natMod
  let r := ((t.comp PortMachine.reverseListPoly).pair
    (v.pair ((p.pair cd).comp Poly.natSub))).comp (ExpandMachine.lookupPoly d)
  let rv := r.comp (Poly.fst natBits natBits)
  let rp := r.comp (Poly.snd natBits natBits)
  let out := (((rp.pair cd).comp Poly.natAdd).pair
    ((c.pair rv).comp Poly.natMul)).comp Poly.natAdd
  exact (((p.pair cd).comp Poly.natLt).ite i out).congr (fun _ => by
    simp only [Function.comp_apply,reverse,decide_eq_true_eq])

noncomputable def relationPoly {d : ℕ} : Poly (prodBits (PortMachine.code (q := d)) natBits) relationCode relation := by
  let ec := PortMachine.code (q := d)
  let t := Poly.fst ec natBits
  let i := Poly.snd ec natBits
  let c := Poly.const (prodBits ec natBits) natBits (2*d)
  let cd := Poly.const (prodBits ec natBits) natBits d
  let v := (i.pair c).comp Poly.natDiv
  let p := (i.pair c).comp Poly.natMod
  let idx := (((p.pair cd).comp Poly.natSub).pair ((cd.pair v).comp Poly.natMul)).comp Poly.natAdd
  exact (((p.pair cd).comp Poly.natLt).ite (Poly.const _ relationCode RegularMachine.trueRelation)
    ((t.pair idx).comp PortMachine.relationPoly)).congr (fun _ => by
      simp only [Function.comp_apply,relation,decide_eq_true_eq])

 theorem reverse_source {d : ℕ} (T : PortTables.Input d) (i : Fin ((output T).1*(2*d))) :
    reverse (T,i.val) = (output T).2.reverseIndex[i].val := by
  let E := (Equiv.prodCongr (Equiv.refl (Fin T.1)) (lazyPorts d)).trans (PortTables.rowIndex _ _)
  obtain ⟨⟨v,b,p⟩,rfl⟩ := E.surjective i
  have hi : ((E (v,b,p)).val/(2*d),(E (v,b,p)).val%(2*d)) = (v.val,(lazyPorts d (b,p)).val) :=
    congrArg (fun z : Fin T.1 × Fin (2*d) => (z.1.val,z.2.val))
      ((PortTables.rowIndex _ _).symm_apply_apply (v,lazyPorts d (b,p)))
  change _ = (lazy T.2).reverseIndex[PortTables.rowIndex _ _ (v,lazyPorts d (b,p))].val
  dsimp only [reverse]
  have hv : (E (v,b,p)).val/(2*d) = v.val := congrArg Prod.fst hi
  have hp : (E (v,b,p)).val%(2*d) = (lazyPorts d (b,p)).val := congrArg Prod.snd hi
  conv_lhs => rw [hv,hp]
  rw [← PortTables.rowIndex_rotation]
  cases b with
  | false =>
    rw [lazyPorts_false_val,ite_eq_left p.isLt,lazy_rotation_false]
    rfl
  | true =>
    rw [lazyPorts_true_val,ite_eq_right (by omega),Nat.add_sub_cancel_right,OverlayMachine.lookup_port T.2 (v,p),
      lazy_rotation_true]
    simp only [PortTables.rowIndex_val,lazyPorts_true_val]

 theorem relation_source {d : ℕ} (T : PortTables.Input d) (i : Fin ((output T).1*(2*d))) :
    relation (T,i.val) = (output T).2.relations[i] := by
  let E := (Equiv.prodCongr (Equiv.refl (Fin T.1)) (lazyPorts d)).trans (PortTables.rowIndex _ _)
  obtain ⟨⟨v,b,p⟩,rfl⟩ := E.surjective i
  have hi : ((E (v,b,p)).val/(2*d),(E (v,b,p)).val%(2*d)) = (v.val,(lazyPorts d (b,p)).val) :=
    congrArg (fun z : Fin T.1 × Fin (2*d) => (z.1.val,z.2.val))
      ((PortTables.rowIndex _ _).symm_apply_apply (v,lazyPorts d (b,p)))
  change _ = (lazy T.2).relations[PortTables.rowIndex _ _ (v,lazyPorts d (b,p))]
  dsimp only [relation]
  have hv : (E (v,b,p)).val/(2*d) = v.val := congrArg Prod.fst hi
  have hp : (E (v,b,p)).val%(2*d) = (lazyPorts d (b,p)).val := congrArg Prod.snd hi
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
  intro a c
  cases b with
  | false =>
    rw [lazyPorts_false_val,ite_eq_left p.isLt,RegularMachine.trueRelation,GraphTables.relationAt_relationOf]
    exact (lazy_accepts_false T.2 v p a c).symm
  | true =>
    rw [lazyPorts_true_val,ite_eq_right (by omega),Nat.add_sub_cancel_right,
      List.getD_eq_getElem _ _ (by simpa using (PortTables.rowIndex T.1 d (v,p)).isLt)]
    exact (lazy_accepts_true T.2 v p a c).symm

noncomputable def poly {d : ℕ} : Poly (PortMachine.code (q := d)) PortMachine.code output := by
  let zero : PortTables.Input d := ⟨0,PortTables.ofPortGraph
    {rot := Equiv.refl _,rot_involutive := fun _ => rfl} (fun _ _ _ => true) (fun _ _ _ => rfl)⟩
  exact PortMachine.materializePoly PortMachine.code zero output PortMachine.verticesPoly
    reversePoly relationPoly reverse_source relation_source

end VertexCover.Machine.LazyMachine
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
