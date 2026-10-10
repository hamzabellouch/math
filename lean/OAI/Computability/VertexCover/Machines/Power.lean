import Mathlib
import OAI.Computability.VertexCover.Machines.PowerRow

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

namespace VertexCover.Machine.PowerMachine
open UniqueGames.Foundations.PCP
open PoweringLabels PoweringEnumeration PoweringTables PowerRowMachine

 theorem relation_ext {q : ℕ} {r s : GenericGraphTables.RelationTable q}
    (h : ∀ a b, GenericGraphTables.relationAt r a b = GenericGraphTables.relationAt s a b) : r=s := by
  apply Vector.ext
  intro i hi
  let ab := (GenericGraphTables.relationIndex q).symm (⟨i,hi⟩ : Fin (q*q))
  have he : GenericGraphTables.relationIndex q ab = (⟨i,hi⟩ : Fin (q*q)) :=
    (GenericGraphTables.relationIndex q).apply_symm_apply _
  have hp := h ab.1 ab.2
  simpa only [GenericGraphTables.relationAt,he,Fin.getElem_fin] using hp

 theorem local_source {d : ℕ} (n : ℕ) (T : PortTables.Input d) (v : Fin T.1)
    (p : Fin (n+1) → Fin d) (b : Bool) :
    localRow n (dartBlockEquiv d n (p,b)) (T,v.val) =
      GenericMachine.rowData (table T.2 n).rows[dartEquiv T.1 d n (b,(v,p))] := by
  apply Prod.ext
  · apply Prod.ext
    · change (localRow n (dartBlockEquiv d n (p,b)) (T,v.val)).1.1 =
        ((GenericGraphTables.semantics (table T.2 n)).tail (dartEquiv T.1 d n (b,(v,p)))).val
      rw [semantics_table]
      simp only [localRow,Equiv.symm_apply_apply,GenericGraphTables.enumeratedGraph,
        mathematicalGraph,PoweringTest.poweredGraph,Equiv.refl_apply]
      cases b with
      | false => rfl
      | true => exact congrArg Prod.snd (NatWalkMachine.word_forget (n+1) p (⟨T,v⟩ : WalkMachine.State d))
    · change (localRow n (dartBlockEquiv d n (p,b)) (T,v.val)).1.2 =
        ((GenericGraphTables.semantics (table T.2 n)).reverse (dartEquiv T.1 d n (b,(v,p)))).val
      rw [semantics_table]
      change (localRow n (dartBlockEquiv d n (p,b)) (T,v.val)).1.2 =
        (dartEquiv T.1 d n (PoweringTest.reverseDart (Fin T.1) (Fin d) n
          ((dartEquiv T.1 d n).symm (dartEquiv T.1 d n (b,(v,p)))))).val
      rw [Equiv.symm_apply_apply]
      simp only [localRow,Equiv.symm_apply_apply,PoweringTest.reverseDart]
      rw [dartEquiv_val,dartBlockEquiv_val,Nat.add_assoc]
      rfl
  · apply relation_ext
    intro a b'
    change GenericGraphTables.relationAt (localRow n (dartBlockEquiv d n (p,b)) (T,v.val)).2 a b' =
      (GenericGraphTables.semantics (table T.2 n)).accepts (dartEquiv T.1 d n (b,(v,p))) a b'
    rw [semantics_table]
    simp only [localRow,Equiv.symm_apply_apply,GenericGraphTables.relationAt_relationOf,
      GenericGraphTables.enumeratedGraph,mathematicalGraph,PoweringTest.poweredGraph]
    cases b <;> exact NatPathMachine.path_source n p _ _ (⟨T,v⟩ : WalkMachine.State d)

 theorem row_source {d : ℕ} (hd : 0<d) (n : ℕ) (T : PortTables.Input d)
    (i : Fin (table T.2 n).darts) :
    row hd n (T,i.val) = GenericMachine.rowData (table T.2 n).rows[i] := by
  obtain ⟨⟨b,v,p⟩,rfl⟩ := (dartEquiv T.1 d n).surjective i
  let j := dartBlockEquiv d n (p,b)
  have hval : (dartEquiv T.1 d n (b,(v,p))).val = j.val+(2*d^(n+1))*v.val := rfl
  have hB : 0<2*d^(n+1) := Nat.mul_pos (by decide) (Nat.pow_pos hd)
  have hv : (dartEquiv T.1 d n (b,(v,p))).val/(2*d^(n+1)) = v.val := by
    rw [hval,Nat.add_mul_div_left _ _ hB,Nat.div_eq_of_lt j.isLt,Nat.zero_add]
  have hj : (⟨(dartEquiv T.1 d n (b,(v,p))).val%(2*d^(n+1)),Nat.mod_lt _ hB⟩ : Block d n) = j := by
    apply Fin.ext
    change (dartEquiv T.1 d n (b,(v,p))).val%(2*d^(n+1)) = j.val
    rw [hval,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt j.isLt]
  unfold row
  conv_lhs => rw [hv,hj]
  exact local_source n T v p b

noncomputable def poly {d : ℕ} (hd : 0<d) (n : ℕ) :
    Poly (PortMachine.code (q := d)) GenericMachine.code (fun T => table T.2 n) := by
  let zero : PortTables.Input d := ⟨0,PortTables.ofPortGraph
    {rot := Equiv.refl _,rot_involutive := fun _ => rfl} (fun _ _ _ => true) (fun _ _ _ => rfl)⟩
  let size := ((Poly.const (PortMachine.code (q := d)) natBits 2).pair PortMachine.verticesPoly).comp Poly.natMul
  let darts := (size.pair (Poly.const _ natBits (d^(n+1)))).comp Poly.natMul
  exact GenericMachine.materializePoly PortMachine.code zero (fun T => table T.2 n)
    PortMachine.verticesPoly darts (rowPoly hd n) (row_source hd n)

end VertexCover.Machine.PowerMachine
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
