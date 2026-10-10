import Mathlib
import OAI.Computability.QuantumFactoring.BooleanVector
import OAI.Computability.QuantumFactoring.NetworkEmissionPack

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def emptyAt (n : ℕ) : Pack:=selectPack n [] (by simp)
def bitPack (n i : ℕ) : Pack:=selectPack n [min n i] (by simp)
def constantPack (n : ℕ) (b : Bool) : Pack:=nodePack n (.constant b) trivial
def bnotPack (a : Pack) : Pack:=compPack a (nodePack 1 (.neg 0) (by simp [Node.Bound]))
def bandPack (a b : Pack) : Pack:=compPack (pairPack a b) (nodePack 2 (.conj 0 1) (by simp [Node.Bound]))
def vectorPack (n : ℕ) (xs : List Pack) : Pack:=xs.foldl pairPack (emptyAt n)
lemma vectorPack_inputs (n : ℕ) (xs : List Pack) : (vectorPack n xs).val.value.inputs=n:=by
  unfold vectorPack
  suffices ∀a:Pack,(xs.foldl pairPack a).val.value.inputs=a.val.value.inputs by exact this _
  intro a
  induction xs generalizing a with
  | nil=>rfl
  | cons b xs ih=>rw [List.foldl_cons,ih,pairPack_inputs]
lemma vectorPack_value {n m : ℕ} (f : Fin m→BooleanNetwork n 1) (p : Fin m→Pack)
    (hp : ∀i,(p i).val.value=erase (f i)) :
    (vectorPack n (List.ofFn p)).val.value=erase (BooleanNetwork.vector f):=by
  induction m with
  | zero=>rfl
  | succ m ih=>
    rw [BooleanNetwork.vector,erase_pair,List.ofFn_succ_last]
    change ((List.ofFn (fun i:Fin m=>p i.castSucc)++[p (Fin.last m)]).foldl pairPack (emptyAt n)).val.value=_
    rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (pairPack (vectorPack n (List.ofFn fun i:Fin m=>p i.castSucc)) (p (Fin.last m))).val.value=_
    rw [pairPack_value,ih (fun i=>f i.castSucc) (fun i=>p i.castSucc) (fun i=>hp i.castSucc),hp]
    rw [vectorPack_inputs,hp];rfl
lemma bitPack_value {n : ℕ} (i : Fin n) : (bitPack n i.val).val.value=erase (BooleanNetwork.bit i):=by
  rw [erase_bit]
  simp only [bitPack,selectPack,min_eq_right (Nat.le_of_lt i.isLt),bit]
lemma constantPack_value (n : ℕ) (b : Bool) : (constantPack n b).val.value=erase (BooleanNetwork.constant (n:=n) b):=by
  rw [erase_constant];rfl
lemma bnotPack_value {n : ℕ} (a : Pack) (f : BooleanNetwork n 1) (h : a.val.value=erase f) :
    (bnotPack a).val.value=erase f.bnot:=by
  rw [erase_bnot,bnotPack,compPack_value]
  · rw [h];rfl
  · rw [h];simp [erase,nodePack,node]
lemma bandPack_value {n : ℕ} (a b : Pack) (f g : BooleanNetwork n 1)
    (ha : a.val.value=erase f) (hb : b.val.value=erase g) :
    (bandPack a b).val.value=erase (f.band g):=by
  have hp : (pairPack a b).val.value=erase (f.pair g):=by
    rw [pairPack_value,ha,hb,erase_pair]
    rw [ha,hb];rfl
  rw [erase_band,bandPack,compPack_value]
  · rw [hp,erase_pair];rfl
  · rw [hp];simp [erase,nodePack,node]
namespace Emission
noncomputable def emptyAtP : Procedure unaryCode packCode emptyAt:=by
  let v:=selectP.comp (unaryToBits.pair (Procedure.constant _ (listCode Nat.bits) []))
  exact ((identity unaryCode).pair v).result (by intro n;rfl)
noncomputable def bitPackP : Procedure (prodCode unaryCode Nat.bits) packCode (fun x=>bitPack x.1 x.2):=by
  let n:=first unaryCode Nat.bits
  let i:=second unaryCode Nat.bits
  let nb:=unaryToBits.comp n
  let idx:=conditional (binaryLt.comp (nb.pair i)) nb i
  let v:=bitP.comp (nb.pair idx)
  exact ((unarySuccessor.comp n).pair v).result (by
    intro x
    simp only [Function.comp_apply,id_eq,decide_eq_true_eq]
    by_cases h : x.1<x.2
    · simp only [h,↓reduceIte,bitPack,selectPack,packCode,bit,prodCode,
        min_eq_left (Nat.le_of_lt h),List.length_singleton,Nat.succ_eq_add_one]
    · simp only [h,↓reduceIte,bitPack,selectPack,packCode,bit,prodCode,
        min_eq_right (by omega : x.2≤x.1),List.length_singleton,Nat.succ_eq_add_one])
noncomputable def constantPackP : Procedure (prodCode unaryCode boolCode) packCode (fun x=>constantPack x.1 x.2):=by
  let n:=first unaryCode boolCode
  let v:=constantP.comp ((unaryToBits.comp n).pair (second unaryCode boolCode))
  let b:=unaryAdd.comp (n.pair (Procedure.constant _ unaryCode 2))
  exact (b.pair v).result (by intro x;rfl)
noncomputable def bnotPackP : Procedure packCode packCode bnotPack:=
  compPackP.comp ((identity packCode).pair (Procedure.constant _ packCode (nodePack 1 (.neg 0) (by simp [Node.Bound]))))
noncomputable def bandPackP : Procedure (prodCode packCode packCode) packCode (fun x=>bandPack x.1 x.2):=
  compPackP.comp (pairPackP.pair (Procedure.constant _ packCode (nodePack 2 (.conj 0 1) (by simp [Node.Bound]))))
noncomputable def vectorPackP : Procedure (prodCode unaryCode (listCode packCode)) packCode
    (fun x=>vectorPack x.1 x.2):=
  foldPairP.comp ((second unaryCode (listCode packCode)).pair (emptyAtP.comp (first unaryCode (listCode packCode))))
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
