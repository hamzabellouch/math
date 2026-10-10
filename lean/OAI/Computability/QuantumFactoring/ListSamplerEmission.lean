import Mathlib
import OAI.Computability.QuantumFactoring.NetworkSequenceEmission
import OAI.Computability.QuantumFactoring.BitStackPowers

namespace OAI



section

namespace ExactQuantumFactoring.ListSamplerEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma work (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>ListSampler.work (n x)):=
  hn.unaryMul (((const _ _ 49).unaryMul hn).unaryAdd (const _ _ 8))
lemma width (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>ListSampler.width (n x)):=
  (hn.unaryAdd hn).unaryAdd (hn.unaryAdd (work hn))
lemma mask (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>listMaskNet (n x)):=by
  apply vectorOfFn hn hn
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  have hN:=hn.comp hx.snd
  exact wordLt (wordConst hN hN ((const _ Nat.bits 2).natPow hx.fst)) (identity hN) hN

def maskOp (n i : ℕ) : Op:=⟨⟨.hadamard,false,true⟩,[i,n+i]⟩
lemma erase_maskGate (n : ℕ) (i : Fin n) : eraseOp (maskGate n i)=maskOp n i.val:=rfl
lemma erase_maskedPrefix (n k : ℕ) (h : k≤n) :
    (maskedPrefix n k h).map eraseOp=(List.range k).map (maskOp n):=by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [maskedPrefix,List.map_append,ih,List.range_succ,List.map_append];rfl
noncomputable def maskOpP : Procedure (prodCode Nat.bits Nat.bits) opCode (fun x=>maskOp x.1 x.2):=by
  let he:=BitStackProgram.Emits.id (prodCode Nat.bits Nat.bits)
  have hwire:=he.snd.listCons ((he.fst.natAdd he.snd).listCons (const _ _ []))
  exact Classical.choice ((ofProcedure CircuitEmission.Emission.opPackP).comp ((const _ _ (⟨.hadamard,false,true⟩ : Gate)).pair hwire))
lemma masked (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>maskedPrefix (n x) (n x) le_rfl):=by
  have h:=(ofProcedure (Procedure.listMapWith (f:=maskOp) 0 (maskOp 0 0) maskOpP)).comp (hn.unaryNat.pair hn.range)
  exact h.congr (fun _=>(erase_maskedPrefix _ _ _).symm)
lemma program (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>ListSampler.circuit (n x)):=by
  have hx:=BitStackProgram.Emits.id (prodCode ea Nat.bits)
  exact (OpsEmits.oracleOn (mask hn) (fun x=>(listMaskNet_count (n x)).trans (Nat.le_add_left _ _))).append
    (OpsEmits.place (masked hn) (fun x=>ListSampler.maskRegister (n x)) (fun x i=>n x+i)
      (fun _ _=>ListSampler.maskRegister_val _ _) ((hn.comp hx.fst).unaryNat.natAdd hx.snd))
lemma singleZero (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalListSlots.singleZeroNet (n x)):=by
  let p : α→ℕ→Pack:=fun x i=>if i<n x then bitPack (n x) i else constantPack (n x) false
  have hx:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hN:=hn.comp hx.snd
  have hi:=hx.fst.unaryNat
  have hp : Emits (prodCode unaryCode ea) packCode (fun x=>p x.2 x.1):=by
    exact ((hi.natLt hN.unaryNat).ite
      ((ofProcedure NetworkEmission.Emission.bitPackP).comp (hN.pair hi))
      ((ofProcedure NetworkEmission.Emission.constantPackP).comp (hN.pair (const _ _ false)))).congr
      (by intro x;simp only [p,decide_eq_true_eq])
  apply vectorIndexed hn (width hn) p hp
  intro x i
  dsimp only [p]
  split
  · rename_i hi
    exact bitPack_value (⟨i.val,hi⟩ : Fin (n x))
  · exact constantPack_value _ _
end ExactQuantumFactoring.ListSamplerEmission

end



end OAI
