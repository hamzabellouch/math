import Mathlib
import OAI.Computability.QuantumFactoring.ModularMultiply
import OAI.Computability.QuantumFactoring.NetworkEmissionVector
import OAI.Computability.QuantumFactoring.RawListRange
import OAI.Computability.QuantumFactoring.BitStackTestBit

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
lemma pairPack_spec {n m l : ℕ} (a b : Pack) (f : BooleanNetwork n m) (g : BooleanNetwork n l)
    (ha : a.val.value=erase f) (hb : b.val.value=erase g) :
    (pairPack a b).val.value=erase (f.pair g):=by
  rw [pairPack_value,ha,hb,erase_pair]
  rw [ha,hb];rfl
lemma compPack_spec {n m l : ℕ} (a b : Pack) (f : BooleanNetwork n m) (g : BooleanNetwork m l)
    (ha : a.val.value=erase f) (hb : b.val.value=erase g) :
    (compPack a b).val.value=erase (f.comp g):=by
  rw [compPack_value,ha,hb,erase_comp]
  rw [ha,hb];simp [erase]
def borPack (a b : Pack) : Pack:=bnotPack (bandPack (bnotPack a) (bnotPack b))
def bxorPack (a b : Pack) : Pack:=borPack (bandPack a (bnotPack b)) (bandPack (bnotPack a) b)
def muxPack (c a b : Pack) : Pack:=borPack (bandPack c a) (bandPack (bnotPack c) b)
lemma borPack_value {n : ℕ} (a b : Pack) (f g : BooleanNetwork n 1)
    (ha : a.val.value=erase f) (hb : b.val.value=erase g) :
    (borPack a b).val.value=erase (f.bor g):=
  bnotPack_value _ _ (bandPack_value _ _ _ _ (bnotPack_value _ _ ha) (bnotPack_value _ _ hb))
lemma bxorPack_value {n : ℕ} (a b : Pack) (f g : BooleanNetwork n 1)
    (ha : a.val.value=erase f) (hb : b.val.value=erase g) :
    (bxorPack a b).val.value=erase (f.bxor g):=
  borPack_value _ _ _ _ (bandPack_value _ _ _ _ ha (bnotPack_value _ _ hb))
    (bandPack_value _ _ _ _ (bnotPack_value _ _ ha) hb)
lemma muxPack_value {n : ℕ} (c a b : Pack) (f g h : BooleanNetwork n 1)
    (hc : c.val.value=erase f) (ha : a.val.value=erase g) (hb : b.val.value=erase h) :
    (muxPack c a b).val.value=erase (BooleanNetwork.mux f g h):=
  borPack_value _ _ _ _ (bandPack_value _ _ _ _ hc ha)
    (bandPack_value _ _ _ _ (bnotPack_value _ _ hc) hb)

def wordConstPack (n w c : ℕ) : Pack:=vectorPack n ((List.range w).map (fun i=>constantPack n (c.testBit i)))
lemma wordConstPack_value (n w c : ℕ) : (wordConstPack n w c).val.value=
    erase (BitArithmetic.wordConstant (n:=n) (BitVec.ofNat w c)):=by
  unfold wordConstPack BitArithmetic.wordConstant
  rw [←ofFn_val_range,List.map_ofFn]
  apply vectorPack_value
  intro i
  dsimp only [Function.comp_apply]
  simpa [←BitVec.getLsbD_eq_getElem,BitVec.getLsbD_ofNat,i.isLt] using constantPack_value n (c.testBit i.val)

def wordMuxPack (w : ℕ) (c a b : Pack) : Pack:=
  compPack (pairPack (pairPack c a) b) (vectorPack (1+w+w) ((List.range w).map (fun i=>
    muxPack (bitPack (1+w+w) 0) (bitPack (1+w+w) (1+i)) (bitPack (1+w+w) (1+w+i)))))
lemma wordMuxPack_value {n w : ℕ} (c a b : Pack) (f : BooleanNetwork n 1) (g h : BooleanNetwork n w)
    (hc : c.val.value=erase f) (ha : a.val.value=erase g) (hb : b.val.value=erase h) :
    (wordMuxPack w c a b).val.value=erase (BitArithmetic.wordMux f g h):=by
  unfold wordMuxPack BitArithmetic.wordMux
  apply compPack_spec _ _ _ _ (pairPack_spec _ _ _ _ (pairPack_spec _ _ _ _ hc ha) hb)
  rw [←ofFn_val_range,List.map_ofFn]
  apply vectorPack_value
  intro i
  exact muxPack_value _ _ _ _ _ _ (bitPack_value ⟨0,by omega⟩)
    (bitPack_value ⟨1+i.val,by omega⟩) (bitPack_value ⟨1+w+i.val,by omega⟩)
namespace Emission
noncomputable def borPackP : Procedure (prodCode packCode packCode) packCode (fun x=>borPack x.1 x.2):=
  bnotPackP.comp (bandPackP.comp (bnotPackP.parallel bnotPackP))
noncomputable def bxorPackP : Procedure (prodCode packCode packCode) packCode (fun x=>bxorPack x.1 x.2):=by
  let a:=first packCode packCode
  let b:=second packCode packCode
  exact borPackP.comp ((bandPackP.comp (a.pair (bnotPackP.comp b))).pair
    (bandPackP.comp ((bnotPackP.comp a).pair b)))
noncomputable def muxPackP : Procedure (prodCode packCode (prodCode packCode packCode)) packCode
    (fun x=>muxPack x.1 x.2.1 x.2.2):=by
  let c:=first packCode (prodCode packCode packCode)
  let a:=(first packCode packCode).comp (second packCode (prodCode packCode packCode))
  let b:=(second packCode packCode).comp (second packCode (prodCode packCode packCode))
  exact borPackP.comp ((bandPackP.comp (c.pair a)).pair (bandPackP.comp ((bnotPackP.comp c).pair b)))
noncomputable def wordConstPackP : Procedure (prodCode unaryCode (prodCode unaryCode Nat.bits)) packCode
    (fun x=>wordConstPack x.1 x.2.1 x.2.2):=by
  let idx:=first unaryCode (prodCode unaryCode Nat.bits)
  let e:=second unaryCode (prodCode unaryCode Nat.bits)
  let n:=(first unaryCode Nat.bits).comp e
  let c:=(second unaryCode Nat.bits).comp e
  let step:=constantPackP.comp (n.pair (testBit.comp (c.pair idx)))
  let n₀:=first unaryCode (prodCode unaryCode Nat.bits)
  let rest:=second unaryCode (prodCode unaryCode Nat.bits)
  let c₀:=(second unaryCode Nat.bits).comp rest
  let w₀:=(first unaryCode Nat.bits).comp rest
  let parts:=(tabulate (f:=fun (x:ℕ×ℕ) i=>constantPack x.1 (x.2.testBit i)) emptyPack step).comp (w₀.pair (n₀.pair c₀))
  exact vectorPackP.comp (n₀.pair parts)
noncomputable def muxVectorPackP : Procedure unaryCode packCode
    (fun w=>vectorPack (1+w+w) ((List.range w).map (fun i=>muxPack (bitPack (1+w+w) 0)
      (bitPack (1+w+w) (1+i)) (bitPack (1+w+w) (1+w+i))))):=by
  let i:=unaryToBits.comp (first unaryCode unaryCode)
  let w:=second unaryCode unaryCode
  let width:=unarySuccessor.comp (unaryAdd.comp (w.pair w))
  let c:=bitPackP.comp (width.pair (Procedure.constant _ Nat.bits 0))
  let a:=bitPackP.comp (width.pair (successor.comp i))
  let b:=bitPackP.comp (width.pair (successor.comp (binaryAdd.comp ((unaryToBits.comp w).pair i))))
  let step:=muxPackP.comp (c.pair (a.pair b))
  let parts:=(tabulate (f:=fun w i=>muxPack (bitPack (1+w+w) 0) (bitPack (1+w+w) (1+i))
    (bitPack (1+w+w) (1+w+i))) emptyPack (step.congrFun (by intro x;simp only [Function.comp_apply,id_eq,Nat.succ_eq_add_one]; simp only [Nat.add_assoc,Nat.add_comm]))).comp
    ((identity unaryCode).pair (identity unaryCode))
  let width₀:=unarySuccessor.comp (unaryAdd.comp ((identity unaryCode).pair (identity unaryCode)))
  exact (vectorPackP.comp (width₀.pair parts)).congrFun (by intro w;simp only [Function.comp_apply,id_eq,Nat.succ_eq_add_one]; simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm])
noncomputable def wordMuxPackP : Procedure (prodCode unaryCode (prodCode packCode (prodCode packCode packCode))) packCode
    (fun x=>wordMuxPack x.1 x.2.1 x.2.2.1 x.2.2.2):=by
  let rest:=second unaryCode (prodCode packCode (prodCode packCode packCode))
  let c:=(first packCode (prodCode packCode packCode)).comp rest
  let ab:=(second packCode (prodCode packCode packCode)).comp rest
  let a:=(first packCode packCode).comp ab
  let b:=(second packCode packCode).comp ab
  exact compPackP.comp ((pairPackP.comp ((pairPackP.comp (c.pair a)).pair b)).pair
    (muxVectorPackP.comp (first unaryCode (prodCode packCode (prodCode packCode packCode)))))
end Emission
end ExactQuantumFactoring.NetworkEmission

end


end OAI
