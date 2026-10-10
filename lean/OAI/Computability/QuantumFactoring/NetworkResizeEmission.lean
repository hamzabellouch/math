import Mathlib
import OAI.Computability.QuantumFactoring.ExpressionSyntaxEmission

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def resizePack (u w : ℕ) : Pack:=vectorPack u ((List.range w).map
  (fun i=>if i<u then bitPack u i else constantPack u false))
lemma resizePack_value (u w : ℕ) : (resizePack u w).val.value=erase (BitArithmetic.resizeWord u w):=by
  unfold resizePack BitArithmetic.resizeWord
  rw [←ofFn_val_range,List.map_ofFn]
  apply vectorPack_value
  intro i
  dsimp only [Function.comp_apply]
  by_cases h : i.val<u
  · simp only [h,↓reduceIte,↓reduceDIte]
    exact bitPack_value ⟨i.val,h⟩
  · simp only [h,↓reduceIte,↓reduceDIte]
    exact constantPack_value _ _
namespace Emission
noncomputable def resizePackP : Procedure (prodCode unaryCode unaryCode) packCode (fun x=>resizePack x.1 x.2):=by
  let i:=unaryToBits.comp (first unaryCode unaryCode)
  let u:=second unaryCode unaryCode
  let test:=binaryLt.comp (i.pair (unaryToBits.comp u))
  let step:=conditional test (bitPackP.comp (u.pair i))
    (constantPackP.comp (u.pair (Procedure.constant _ boolCode false)))
  let step' : Procedure (prodCode unaryCode unaryCode) packCode
      (fun x=>if x.1<x.2 then bitPack x.2 x.1 else constantPack x.2 false):=
    step.congrFun (by intro x;simp only [Function.comp_apply,decide_eq_true_eq,id_eq])
  let xs:=(tabulate (f:=fun u i=>if i<u then bitPack u i else constantPack u false) emptyPack step').comp ((second unaryCode unaryCode).pair (first unaryCode unaryCode))
  exact vectorPackP.comp ((first unaryCode unaryCode).pair xs)
noncomputable def exprWidthP {vars : Type} (ev : vars→List Bool) : Procedure (prodCode unaryCode (exprCode ev)) unaryCode
    (fun x=>x.2.templateWidth x.1):=by
  let b:=first unaryCode (exprCode ev)
  let e:=second unaryCode (exprCode ev)
  let sz:=(exprSizeP ev).comp e
  let mc:=(exprMaxP ev).comp e
  let sizeP : Procedure Nat.bits unaryCode Nat.size:=
    (Procedure.length.precompose Nat.bits).congrFun (by intro n;exact n.size_eq_bits_len)
  let bitlen:=sizeP.comp mc
  exact unaryMul.comp ((unarySuccessor.comp (unaryAdd.comp (b.pair bitlen))).pair sz)
end Emission
end ExactQuantumFactoring.NetworkEmission

end


end OAI
