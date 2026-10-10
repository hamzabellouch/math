import Mathlib
import OAI.Computability.QuantumFactoring.BitStackSubtractor

namespace OAI

section
namespace ExactQuantumFactoring.BitStackProgram

namespace Procedure
noncomputable def subStepP : Procedure subStateCode subStateCode subStep := by
  let x:=first (id : List Bool→List Bool) (prodCode id (prodCode boolCode id))
  let rem:=second (id : List Bool→List Bool) (prodCode id (prodCode boolCode id))
  let y:=(first (id : List Bool→List Bool) (prodCode boolCode id)).comp rem
  let co:=(second (id : List Bool→List Bool) (prodCode boolCode id)).comp rem
  let c:=(first boolCode (id : List Bool→List Bool)).comp co
  let zs:=(second boolCode (id : List Bool→List Bool)).comp co
  let bits:=(head.comp x).pair ((head.comp y).pair c)
  let newc:=(ofBool₃ boolCode borrowBit).comp bits
  let newb:=(ofBool₃ boolCode sumBit).comp bits
  exact ((tail.comp x).pair ((tail.comp y).pair
    (newc.pair (cons.comp (newb.pair zs))))).congrFun (by intro s;rfl)

noncomputable def wordSubtractP :
    Procedure (prodCode (id : List Bool→List Bool) id) (prodCode boolCode id) wordSubtract := by
  let x:=first (id : List Bool→List Bool) (id : List Bool→List Bool)
  let y:=second (id : List Bool→List Bool) (id : List Bool→List Bool)
  let len:=unarySuccessor.comp (unaryAdd.comp ((length.comp x).pair (length.comp y)))
  let start:=x.pair (y.pair ((constant (prodCode id id) boolCode false).pair
    (constant (prodCode id id) (id : List Bool→List Bool) [])))
  let rep:=subStepP.iterateLinear 1 subStep_size
  let co:=(second (id : List Bool→List Bool) (prodCode boolCode id)).comp
    (second (id : List Bool→List Bool) (prodCode id (prodCode boolCode id)))
  let c:=(first boolCode (id : List Bool→List Bool)).comp co
  let zs:=(second boolCode (id : List Bool→List Bool)).comp co
  exact ((c.pair (reverse.comp zs)).comp (rep.comp (len.pair start))).congrFun (by intro x;rfl)

noncomputable def binaryLt : Procedure (prodCode Nat.bits Nat.bits) boolCode
    (fun x=>decide (x.1<x.2)) :=
  (((first boolCode (id : List Bool→List Bool)).comp wordSubtractP).precompose
    (fun x : ℕ×ℕ=>(x.1.bits,x.2.bits))).congrFun
      (by
        intro x
        change (wordSubtract (x.1.bits,x.2.bits)).1=decide (x.1<x.2)
        rw [wordSubtract_borrow,binaryValue_bits,binaryValue_bits])

noncomputable def binaryLe : Procedure (prodCode Nat.bits Nat.bits) boolCode
    (fun x=>decide (x.1≤x.2)) :=
  (boolNot.comp (binaryLt.comp (swap Nat.bits Nat.bits))).congrFun (by
    intro x
    change (!(decide (x.2<x.1)))=decide (x.1≤x.2)
    simp only [← decide_not,Nat.not_lt])

noncomputable def binarySub : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun x=>x.1-x.2) :=
  (((choose normalize (constant (id : List Bool→List Bool) Nat.bits 0)).comp
    wordSubtractP).precompose (fun x : ℕ×ℕ=>(x.1.bits,x.2.bits))).congrFun
      (by
        intro x
        change (if (wordSubtract (x.1.bits,x.2.bits)).1 then 0 else
          binaryValue (wordSubtract (x.1.bits,x.2.bits)).2)=x.1-x.2
        rw [wordSubtract_value,binaryValue_bits,binaryValue_bits])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
