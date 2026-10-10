import Mathlib
import OAI.Computability.QuantumFactoring.ArithmeticPredicates
import OAI.Computability.QuantumFactoring.AIGNetworkEmission
import OAI.Computability.QuantumFactoring.AIGNetworkProcedure
import OAI.Computability.QuantumFactoring.NativeAIGBinaryInputs

namespace OAI



section

namespace ExactQuantumFactoring.AIGNetworkEmission
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
open BitStackProgram BitStackProgram.Procedure NetworkEmission

def binaryPack (op : NativeAIG.Graph→List NativeAIG.Ref→List NativeAIG.Ref→NativeAIG.Graph×List NativeAIG.Ref)
    (w : ℕ) : Pack:=
  let r:=op (NativeAIG.rawInputs (w+w)) (NativeAIG.rawWord 0 w) (NativeAIG.rawWord w w)
  compilePack (w+w) r.1.decls r.2
lemma binaryPack_value (op : NativeAIG.Graph→List NativeAIG.Ref→List NativeAIG.Ref→NativeAIG.Graph×List NativeAIG.Ref)
    (w : ℕ) (res : AIG.RefVecEntry (Fin (w+w)) w)
    (hr : NativeAIG.VecRel (op (NativeAIG.rawInputs (w+w)) (NativeAIG.rawWord 0 w) (NativeAIG.rawWord w w)) res) :
    (binaryPack op w).val.value=erase (AIGCompiler.compileVec res.aig res.vec):=by
  dsimp only [binaryPack]
  rw [hr.2]
  exact compilePack_value hr.1 _
lemma addPack_value (w : ℕ) : (binaryPack NativeAIG.add w).val.value=erase (BitArithmetic.add w):=by
  apply binaryPack_value
  have hh:=NativeAIG.add_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
  simpa only [NativeAIG.eraseVec_binaryInputs_lhs,NativeAIG.eraseVec_binaryInputs_rhs] using hh
lemma mulPack_value (w : ℕ) : (binaryPack NativeAIG.mul w).val.value=erase (BitArithmetic.mul w):=by
  apply binaryPack_value
  have hh:=NativeAIG.mul_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
  simpa only [NativeAIG.eraseVec_binaryInputs_lhs,NativeAIG.eraseVec_binaryInputs_rhs] using hh
lemma subPack_value (w : ℕ) : (binaryPack NativeAIG.sub w).val.value=erase (BitArithmetic.sub w):=by
  apply binaryPack_value
  have hh:=NativeAIG.sub_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
  simpa only [NativeAIG.eraseVec_binaryInputs_lhs,NativeAIG.eraseVec_binaryInputs_rhs] using hh
lemma divPack_value (w : ℕ) : (binaryPack NativeAIG.divide w).val.value=erase (BitArithmetic.div w):=by
  apply binaryPack_value
  have hh:=NativeAIG.divide_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
  simpa only [NativeAIG.eraseVec_binaryInputs_lhs,NativeAIG.eraseVec_binaryInputs_rhs] using hh
lemma modPack_value (w : ℕ) : (binaryPack NativeAIG.remainder w).val.value=erase (BitArithmetic.mod w):=by
  apply binaryPack_value
  have hh:=NativeAIG.remainder_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
  simpa only [NativeAIG.eraseVec_binaryInputs_lhs,NativeAIG.eraseVec_binaryInputs_rhs] using hh

def ultPack (w : ℕ) : Pack:=
  let r:=NativeAIG.ult (NativeAIG.rawInputs (w+w)) (NativeAIG.rawWord 0 w) (NativeAIG.rawWord w w)
  compilePack (w+w) r.1.decls [r.2]
lemma ultPack_value (w : ℕ) : (ultPack w).val.value=erase (BitArithmetic.ult w):=by
  have hr:=NativeAIG.ult_rel (NativeAIG.inputs_rel (w+w)) (BitArithmetic.binaryInputs w)
  simp only [NativeAIG.eraseVec_binaryInputs_lhs,NativeAIG.eraseVec_binaryInputs_rhs] at hr
  unfold ultPack BitArithmetic.ult
  have hh:=compilePack_value hr.1 (fun _ : Fin 1=>(Std.Tactic.BVDecide.BVPred.mkUlt
    (AIGCompiler.inputs (w+w)).1 (BitArithmetic.binaryInputs w)).ref)
  simpa only [List.ofFn_succ,List.ofFn_zero,hr.2] using hh

namespace Emission
noncomputable def binaryPackP
    {op : NativeAIG.Graph→List NativeAIG.Ref→List NativeAIG.Ref→NativeAIG.Graph×List NativeAIG.Ref}
    (p : Procedure unaryCode (prodCode NativeAIG.graphCode (listCode NativeAIG.refCode))
      (fun w=>op (NativeAIG.rawInputs (w+w)) (NativeAIG.rawWord 0 w) (NativeAIG.rawWord w w))) :
    Procedure unaryCode packCode (binaryPack op):=by
  let width:=unaryAdd.comp ((identity unaryCode).pair (identity unaryCode))
  let graph:=(first NativeAIG.graphCode (listCode NativeAIG.refCode)).comp p
  let ds:=NativeAIG.Emission.decls.comp graph
  let refs:=(second NativeAIG.graphCode (listCode NativeAIG.refCode)).comp p
  exact compilePackP.comp ((width.pair ds).pair refs)
noncomputable def addPackP : Procedure unaryCode packCode (binaryPack NativeAIG.add):=binaryPackP NativeAIG.Emission.inputAddP
noncomputable def mulPackP : Procedure unaryCode packCode (binaryPack NativeAIG.mul):=binaryPackP NativeAIG.Emission.inputMulP
noncomputable def subPackP : Procedure unaryCode packCode (binaryPack NativeAIG.sub):=binaryPackP NativeAIG.Emission.inputSubP
noncomputable def divPackP : Procedure unaryCode packCode (binaryPack NativeAIG.divide):=binaryPackP NativeAIG.Emission.inputDivP
noncomputable def modPackP : Procedure unaryCode packCode (binaryPack NativeAIG.remainder):=binaryPackP NativeAIG.Emission.inputModP
noncomputable def inputUltP : Procedure unaryCode (prodCode NativeAIG.graphCode NativeAIG.refCode)
    (fun w=>NativeAIG.ult (NativeAIG.rawInputs (w+w)) (NativeAIG.rawWord 0 w) (NativeAIG.rawWord w w)):=by
  refine (NativeAIG.Emission.ultP.comp (((identity NativeAIG.addStateCode).precompose
    (fun s:NativeAIG.BinaryState=>s.val)).comp NativeAIG.Emission.binaryInputP)).congrFun ?_
  intro w
  change NativeAIG.ult (NativeAIG.binaryInput w).val.val.graph (NativeAIG.binaryInput w).val.val.lhs
    (NativeAIG.binaryInput w).val.val.rhs=_
  congr 1
noncomputable def ultPackP : Procedure unaryCode packCode ultPack:=by
  let width:=unaryAdd.comp ((identity unaryCode).pair (identity unaryCode))
  let ds:=NativeAIG.Emission.decls.comp ((first NativeAIG.graphCode NativeAIG.refCode).comp inputUltP)
  let ref:=(second NativeAIG.graphCode NativeAIG.refCode).comp inputUltP
  let refs:=(listCons NativeAIG.refCode).comp (ref.pair (Procedure.constant _ (listCode NativeAIG.refCode) []))
  exact compilePackP.comp ((width.pair ds).pair refs)
end Emission
end ExactQuantumFactoring.AIGNetworkEmission

end


end OAI
