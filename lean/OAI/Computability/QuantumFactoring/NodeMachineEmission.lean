import Mathlib
import OAI.Computability.QuantumFactoring.NetworkRecursionEmission
import OAI.Computability.QuantumFactoring.OpsEmits
import OAI.Computability.QuantumFactoring.MachineWiringEmission

namespace OAI



section

namespace ExactQuantumFactoring.NodeMachineEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n c t : α→ℕ} {M : ∀x,NodeMachine (n x) (c x)}
lemma width (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>NodeKernel.width (n x)))
    (hi : Emits ea unaryCode (fun x=>(M x).initWork)) (hu : Emits ea unaryCode (fun x=>(M x).updateWork))
    (ht : Emits ea unaryCode t) : Emits ea unaryCode (fun x=>(M x).width (t x)):=
  (hc.unaryAdd (ht.unaryMul (((hk.unaryAdd hi).unaryAdd hc).unaryAdd hu))).congr
    (fun x=>((M x).width_eq (t x)).symm)
lemma current (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>NodeKernel.width (n x)))
    (hi : Emits ea unaryCode (fun x=>(M x).initWork)) (hu : Emits ea unaryCode (fun x=>(M x).updateWork))
    (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(M x).currentNet (t x)):=by
  have ht':=(ht.unaryNat.natSub (const _ _ 1)).boundedUnary ht (by intro x;exact Nat.sub_le _ _)
  have hs:=((ht.unaryNat.natEq (const _ _ 0)).ite (const _ Nat.bits 0)
    (((width hc hk hi hu ht').unaryNat.natAdd hk.unaryNat).natAdd hi.unaryNat))
  apply selectSlice (width hc hk hi hu ht) hc hs (fun x=>(M x).current (t x))
  intro x i
  cases h : t x with
  | zero=>simp only [NodeMachine.current,decide_true,ite_true,Nat.zero_add];rfl
  | succ j=>simp only [Nat.succ_ne_zero,decide_false,Nat.add_sub_cancel,NodeMachine.current];rfl
lemma init (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>NodeKernel.width (n x)))
    (hK : NetEmits ea (fun x=>NodeKernel.initialNet (n x)))
    (hQ : NetEmits ea (fun x=>(M x).query)) (hU : NetEmits ea (fun x=>(M x).update))
    (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(M x).initNet (t x)):=
  ((current hc hk (hQ.count.unaryAdd hK.count) hU.count ht).comp hQ).comp hK
lemma update (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>NodeKernel.width (n x)))
    (hK : NetEmits ea (fun x=>NodeKernel.initialNet (n x)))
    (hQ : NetEmits ea (fun x=>(M x).query)) (hU : NetEmits ea (fun x=>(M x).update))
    (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(M x).updateNet (t x)):=by
  have hi:=hQ.count.unaryAdd hK.count
  have hw:=width hc hk hi hU.count ht
  exact (((firstSelect hw hk hi).comp (current hc hk hi hU.count ht)).pair
    (targetSelect hw hk hi)).comp hU
lemma program (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>NodeKernel.width (n x)))
    (hK : NetEmits ea (fun x=>NodeKernel.initialNet (n x)))
    (hP : OpsEmits ea (fun x=>NodeKernel.program (n x)))
    (hQ : NetEmits ea (fun x=>(M x).query)) (hU : NetEmits ea (fun x=>(M x).update))
    (ht : Emits ea unaryCode t) : OpsEmits ea (fun x=>(M x).program (t x)):=by
  have hi:=hQ.count.unaryAdd hK.count
  have hu:=hU.count
  apply OpsEmits.boundedStages ht (f:=fun x j=>(M x).program j)
  · exact const _ _ []
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode (listCode opCode)))).precompose
      (fun x:Σa,Fin (t a)=>(x.1,(x.2.val,((M x.1).program x.2.val).map eraseOp)))
    have hC:=hc.comp hx.fst
    have hKW:=hk.comp hx.fst
    have hKI:=hK.compInput hx.fst
    have hQuery:=hQ.compInput hx.fst
    have hUpdate:=hU.compInput hx.fst
    have hTime:=hx.snd.fst
    have hWidth:=width hC hKW (hi.comp hx.fst) (hu.comp hx.fst) hTime
    exact ((OpsEmits.appendPrepared hx.snd.snd (init hC hKW hKI hQuery hUpdate hTime)
      hWidth (fun x=>((M x.1).initNet_count x.2.val).le) (hP.comp hx.fst)).first
        (fun x=>c x.1) (fun x=>(M x.1).updateWork)).append
      (OpsEmits.oracleOn (update hC hKW hKI hQuery hUpdate hTime)
        (fun x=>((M x.1).updateNet_count x.2.val).le))
  · have hb:=(width hc hk hi hu ht).unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
    exact hb.of_le (by
      intro x
      rw [(M _).width_eq,(M _).width_eq]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)) _)
  · have htime:=ht.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
    have hlen:=(hP.lengthPoly).pull (fun x:Σa,Fin (t a+1)=>x.1)
    have hinit:=hi.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
    have hupdate:=hu.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
    have hkernel:=hk.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
    have hconfig:=hc.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
    exact (htime.mul (((((PolyAt.const _ 4).mul hinit).add ((PolyAt.const _ 2).mul hkernel)).add hlen).add
      ((PolyAt.const _ 4).mul hupdate) |>.add ((PolyAt.const _ 2).mul hconfig))).of_le (by
        intro x
        exact ((M x.1).program_length x.2.val).trans (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)))
lemma initial (hc : Emits ea unaryCode c) (hk : Emits ea unaryCode (fun x=>NodeKernel.width (n x)))
    (hi : Emits ea unaryCode (fun x=>(M x).initWork)) (hu : Emits ea unaryCode (fun x=>(M x).updateWork))
    (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(M x).initialNet (t x)):=by
  apply NetEmits.boundedStages ht (f:=fun x j=>(M x).initialNet j)
  · exact identity hc
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (t a)=>(x.1,(x.2.val,erasePack ((M x.1).initialNet x.2.val))))
    have hprev:=ofCanonical hx.snd.snd
    have hC:=hc.comp hx.fst
    have hKW:=hk.comp hx.fst
    exact ((hprev.packNet (zeros hC hKW) hC (hi.comp hx.fst)).packNet (zeros hC hC) hC (hu.comp hx.fst))
  · exact hc.unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)
  · exact ((width hc hk hi hu ht).unaryPoly.pull (fun x:Σa,Fin (t a+1)=>x.1)).of_le (by
      intro x;rw [(M _).width_eq,(M _).width_eq]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)) _)
  · have hb:=(ht.unaryPoly.mul (((hk.unaryPoly.add hi.unaryPoly).add hc.unaryPoly).add hu.unaryPoly)).pull
      (fun x:Σa,Fin (t a+1)=>x.1)
    exact hb.of_le (by
      intro x
      rw [(M _).initialNet_count]
      exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
end ExactQuantumFactoring.NodeMachineEmission

end


end OAI
