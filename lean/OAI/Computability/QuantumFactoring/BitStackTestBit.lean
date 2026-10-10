import Mathlib
import OAI.Computability.QuantumFactoring.BitStackChoice
import OAI.Computability.QuantumFactoring.BitStackNaturals
import OAI.Computability.QuantumFactoring.BitStackWords

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
noncomputable def dropWord : Procedure (prodCode unaryCode (id : List Bool→List Bool)) id
    (fun x=>x.2.drop x.1):=by
  refine (tail.iterate Polynomial.X ?_).congrFun ?_
  · intro n xs i hi
    have h : (List.tail^[i] xs).length≤xs.length:=by
      induction i with
      | zero=>rfl
      | succ i ih=>
        rw [Function.iterate_succ_apply']
        simp only [List.length_tail]
        omega
    simp only [Polynomial.eval_X,id_eq]
    exact h.trans (Nat.le_add_left _ _)
  · rintro ⟨n,xs⟩
    change List.tail^[n] xs=xs.drop n
    induction n with
    | zero=>rfl
    | succ n ih=> rw [Function.iterate_succ_apply',ih,List.tail_drop]
noncomputable def testBit : Procedure (prodCode Nat.bits unaryCode) boolCode
    (fun x=>x.1.testBit x.2):=by
  let p:=head.comp (dropWord.comp
    ((second Nat.bits unaryCode).pair ((identity (id : List Bool→List Bool)).precompose Nat.bits |>.comp
      (first Nat.bits unaryCode))))
  refine p.congrFun ?_
  intro x
  change (x.1.bits.drop x.2).headD false=x.1.testBit x.2
  rw [Nat.testBit_eq_inth,List.headD_eq_head?_getD,List.head?_drop]
  rfl
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
