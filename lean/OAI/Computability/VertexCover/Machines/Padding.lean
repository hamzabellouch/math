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

namespace VertexCover.Machine.PaddingMachine
open UniqueGames.Foundations.PCP
open PortMachine TableMachine PreprocessingPaddingTables

abbrev Input (q : ℕ) := PortTables.Input q

def padded {q : ℕ} (T : Input q) : Input q :=
  ⟨PreprocessingLevels.paddedSize T.1,pad T.2 (PreprocessingLevels.le_paddedSize T.1)⟩

def reverse {q : ℕ} (x : Input q × ℕ) : ℕ :=
  if x.2 < x.1.1*q then (x.1.2.reverseIndex.toList.map Fin.val).getD x.2 0 else x.2

def relation {q : ℕ} (x : Input q × ℕ) : GraphTables.RelationTable :=
  if x.2 < x.1.1*q then x.1.2.relations.toList.getD x.2 relationDefault else RegularMachine.trueRelation

noncomputable def testPoly {q : ℕ} : Poly (prodBits (code (q := q)) natBits) boolBits
    (fun x => decide (x.2 < x.1.1*q)) := by
  let n := ((Poly.fst (code (q := q)) natBits).comp verticesPoly).pair (Poly.const _ natBits q)
  exact ((Poly.snd code natBits).pair (n.comp Poly.natMul)).comp Poly.natLt

noncomputable def reversePoly {q : ℕ} : Poly (prodBits (code (q := q)) natBits) natBits reverse :=
  testPoly.ite PortMachine.reversePoly (Poly.snd code natBits) |>.congr (fun _ => by
    simp only [reverse,decide_eq_true_eq])

noncomputable def relationPoly {q : ℕ} : Poly (prodBits (code (q := q)) natBits) relationCode relation :=
  testPoly.ite PortMachine.relationPoly (Poly.const _ relationCode RegularMachine.trueRelation) |>.congr
    (fun _ => by simp only [relation,decide_eq_true_eq])

 theorem reverse_source {q : ℕ} (T : Input q) (i : Fin ((padded T).1*q)) :
    reverse (T,i.val) = (padded T).2.reverseIndex[i].val := by
  let h := PreprocessingLevels.le_paddedSize T.1
  let E := (Equiv.prodCongr (vertexEquiv h) (Equiv.refl (Fin q))).trans (PortTables.rowIndex _ q)
  obtain ⟨⟨v,p⟩,rfl⟩ := E.surjective i
  cases v with
  | inl v =>
    have hi : (E (Sum.inl v,p)).val = (PortTables.rowIndex T.1 q (v,p)).val := rfl
    dsimp only [reverse]
    conv_lhs => rw [hi,ite_eq_left (PortTables.rowIndex T.1 q (v,p)).isLt,PortMachine.reverse_valid]
    change _ = (pad T.2 h).reverseIndex[PortTables.rowIndex _ q (v.castLE h,p)].val
    rw [reverseIndex_pad_old]
    exact (congrArg Fin.val (PortTables.rowIndex_rotation T.2 (v,p))).symm
  | inr v =>
    have hi : T.1*q ≤ (E (Sum.inr v,p)).val := by
      change T.1*q ≤ p.val+q*(T.1+v.val)
      nlinarith
    dsimp only [reverse]
    rw [ite_eq_right (by omega)]
    change _ = (pad T.2 h).reverseIndex[PortTables.rowIndex _ q (vertexEquiv h (Sum.inr v),p)].val
    rw [reverseIndex_pad_new]
    rfl

 theorem relation_source {q : ℕ} (T : Input q) (i : Fin ((padded T).1*q)) :
    relation (T,i.val) = (padded T).2.relations[i] := by
  let h := PreprocessingLevels.le_paddedSize T.1
  let E := (Equiv.prodCongr (vertexEquiv h) (Equiv.refl (Fin q))).trans (PortTables.rowIndex _ q)
  obtain ⟨⟨v,p⟩,rfl⟩ := E.surjective i
  cases v with
  | inl v =>
    have hi : (E (Sum.inl v,p)).val = (PortTables.rowIndex T.1 q (v,p)).val := rfl
    dsimp only [relation]
    conv_lhs => rw [hi,ite_eq_left (PortTables.rowIndex T.1 q (v,p)).isLt,PortMachine.relation_valid]
    exact (relations_pad_old T.2 h v p).symm
  | inr v =>
    have hi : T.1*q ≤ (E (Sum.inr v,p)).val := by
      change T.1*q ≤ p.val+q*(T.1+v.val)
      nlinarith
    dsimp only [relation]
    rw [ite_eq_right (by omega)]
    change RegularMachine.trueRelation =
      (pad T.2 h).relations[PortTables.rowIndex _ q (vertexEquiv h (Sum.inr v),p)]
    apply Vector.ext
    intro index indexBound
    let labels := GraphTables.relationIndex.symm ⟨index,indexBound⟩
    have agreement := (accepts_pad_new T.2 h v p labels.1 labels.2).symm
    have true_value : GraphTables.relationAt RegularMachine.trueRelation labels.1 labels.2 = true := by
      rw [RegularMachine.trueRelation,GraphTables.relationAt_relationOf]
    rw [← true_value] at agreement
    simpa only [PortTables.accepts,GraphTables.relationAt,labels,Prod.eta,
      Equiv.apply_symm_apply,Fin.getElem_fin]
      using agreement

noncomputable def poly {q : ℕ} : Poly (code (q := q)) code padded := by
  let zero : Input q := ⟨0,PortTables.ofPortGraph
    {rot := Equiv.refl _,rot_involutive := fun _ => rfl} (fun _ _ _ => true) (fun _ _ _ => rfl)⟩
  exact materializePoly code zero padded (PortMachine.verticesPoly.comp ExpandMachine.paddedSizePoly)
    reversePoly relationPoly reverse_source relation_source

end VertexCover.Machine.PaddingMachine
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
