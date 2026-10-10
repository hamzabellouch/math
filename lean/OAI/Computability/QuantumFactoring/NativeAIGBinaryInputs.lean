import Mathlib
import OAI.Computability.QuantumFactoring.BitArithmetic
import OAI.Computability.QuantumFactoring.RawListRange
import OAI.Computability.QuantumFactoring.NativeAIGMulWrapper
import OAI.Computability.QuantumFactoring.NativeAIGMod
import OAI.Computability.QuantumFactoring.NativeAIGInputs
import OAI.Computability.QuantumFactoring.EmissionFurther2
import OAI.Computability.QuantumFactoring.NativeAIGDivWrapper
import OAI.Computability.QuantumFactoring.NativeAIGModWrapper

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure Std.Sat
lemma rawInputs_bound (n : ℕ) : Bounded (n+1) (rawInputs n):=by
  refine ⟨by simp [rawInputs],by simp [rawInputs],?_,by simp [rawInputs]⟩
  intro d hd
  simp only [rawInputs,List.mem_cons,List.mem_map] at hd
  rcases hd with rfl | ⟨i,hi,rfl⟩
  · trivial
  · have hi:=List.mem_range.mp hi
    change i≤n+1
    omega

def rawWord (offset w : ℕ) : List Ref:=(List.range w).map (fun i=>(offset+i+1,false))
lemma rawWord_bound (o w : ℕ) : RefsBound (o+w+1) (rawWord o w):=by
  refine ⟨by simp [rawWord];omega,?_⟩
  intro a ha
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ha
  have hi:=List.mem_range.mp hi
  dsimp only
  omega
def binaryInput (w : ℕ) : BinaryState:=⟨⟨⟨w+w+1,rawInputs (w+w),rawWord 0 w,rawWord w w,0,(0,false),[]⟩,
  rawInputs_bound _,(rawWord_bound 0 w).mono (by change 0+w+1≤w+w+1;omega),rawWord_bound w w,
  Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩,by simp [rawWord]⟩
lemma eraseVec_binaryInputs_lhs (w : ℕ) : eraseVec (BitArithmetic.binaryInputs w).lhs=rawWord 0 w:=by
  unfold eraseVec BitArithmetic.binaryInputs
  simp only [AIGCompiler.refVector_get,inputs_ref,Fin.val_castAdd]
  rw [rawWord,←ofFn_val_range,List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply,Nat.zero_add]
lemma eraseVec_binaryInputs_rhs (w : ℕ) : eraseVec (BitArithmetic.binaryInputs w).rhs=rawWord w w:=by
  unfold eraseVec BitArithmetic.binaryInputs
  simp only [AIGCompiler.refVector_get,inputs_ref,Fin.val_natAdd]
  rw [rawWord,←ofFn_val_range,List.map_ofFn]
  rfl
namespace Emission
noncomputable def rawWordP : Procedure (prodCode unaryCode unaryCode) (listCode refCode)
    (fun x=>rawWord x.1 x.2):=by
  let p:=(successor.comp (binaryAdd.comp
    ((unaryToBits.comp (second unaryCode unaryCode)).pair (unaryToBits.comp (first unaryCode unaryCode))))).pair
      (Procedure.constant _ boolCode false)
  exact ((tabulate (f:=fun o i=>(o+i+1,false)) (0,false) p).comp
    ((second unaryCode unaryCode).pair (first unaryCode unaryCode))).congrFun (by intro x;rfl)
noncomputable def binaryInputP : Procedure unaryCode binaryStateCode binaryInput:=by
  let w:=identity unaryCode
  let two:=unaryAdd.comp (w.pair w)
  let b:=unarySuccessor.comp two
  let g:=inputsP.comp two
  let l:=rawWordP.comp ((Procedure.constant _ unaryCode 0).pair w)
  let r:=rawWordP.comp (w.pair w)
  exact (packAddP.comp (b.pair (g.pair (l.pair (r.pair
    ((Procedure.constant _ Nat.bits 0).pair ((Procedure.constant _ refCode (0,false)).pair
      (Procedure.constant _ (listCode refCode) [])))))))).result (by intro n;rfl)
noncomputable def inputAddP : Procedure unaryCode (prodCode graphCode (listCode refCode))
    (fun w=>add (rawInputs (w+w)) (rawWord 0 w) (rawWord w w)):=by
  refine (addP.comp (((identity addStateCode).precompose (fun s:BinaryState=>s.val)).comp binaryInputP)).congrFun ?_
  intro w
  change add (binaryInput w).val.val.graph (binaryInput w).val.val.lhs (binaryInput w).val.val.rhs = _
  congr 1
noncomputable def inputMulP : Procedure unaryCode (prodCode graphCode (listCode refCode))
    (fun w=>mul (rawInputs (w+w)) (rawWord 0 w) (rawWord w w)):=by
  refine (mulP.comp binaryInputP).congrFun ?_
  intro w
  change mul (binaryInput w).val.val.graph (binaryInput w).val.val.lhs (binaryInput w).val.val.rhs = _
  congr 1
noncomputable def inputSubP : Procedure unaryCode (prodCode graphCode (listCode refCode))
    (fun w=>sub (rawInputs (w+w)) (rawWord 0 w) (rawWord w w)):=by
  refine (subP.comp binaryInputP).congrFun ?_
  intro w
  change sub (binaryInput w).val.val.graph (binaryInput w).val.val.lhs (binaryInput w).val.val.rhs = _
  congr 1
noncomputable def inputDivP : Procedure unaryCode (prodCode graphCode (listCode refCode))
    (fun w=>divide (rawInputs (w+w)) (rawWord 0 w) (rawWord w w)):=by
  refine (divideP.comp binaryInputP).congrFun ?_
  intro w
  change divide (binaryInput w).val.val.graph (binaryInput w).val.val.lhs (binaryInput w).val.val.rhs = _
  congr 1
noncomputable def inputModP : Procedure unaryCode (prodCode graphCode (listCode refCode))
    (fun w=>remainder (rawInputs (w+w)) (rawWord 0 w) (rawWord w w)):=by
  refine (remainderP.comp binaryInputP).congrFun ?_
  intro w
  change remainder (binaryInput w).val.val.graph (binaryInput w).val.val.lhs (binaryInput w).val.val.rhs = _
  congr 1
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI
