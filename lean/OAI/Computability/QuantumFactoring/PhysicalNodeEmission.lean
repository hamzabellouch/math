import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalSplitDecoderEmission
import OAI.Computability.QuantumFactoring.NodeStateEmission
import OAI.Computability.QuantumFactoring.SortingEmission
import OAI.Computability.QuantumFactoring.SplitMachineEmission

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalNodeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n s t : α→ℕ}
lemma configWidth (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) : Emits ea unaryCode (fun x=>PhysicalNode.configWidth (n x) (s x)):=
  NodeStateEmission.width hs hn.unarySucc
lemma query (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) : NetEmits ea (fun x=>PhysicalNode.query (n x) (s x)):=
  (NodeStateEmission.top hs hn.unarySucc).comp (resize hn.unarySucc hn)
lemma update (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) : NetEmits ea (fun x=>PhysicalNode.update (n x) (s x)):=
  ((left (configWidth hn hs) (PhysicalSplitEmission.width hn)).pair
    ((right (configWidth hn hs) (PhysicalSplitEmission.width hn)).comp (PhysicalSplitEmission.divisor hn))).comp (NodeStateEmission.step hs hn.unarySucc)
lemma initWork (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) : Emits ea unaryCode (fun x=>(PhysicalNode.machine (n x) (s x)).initWork):=
  (query hn hs).count.unaryAdd (PhysicalSplitEmission.initial hn).count
lemma updateWork (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) : Emits ea unaryCode (fun x=>(PhysicalNode.machine (n x) (s x)).updateWork):=(update hn hs).count
lemma width (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (ht : Emits ea unaryCode t) : Emits ea unaryCode (fun x=>(PhysicalNode.machine (n x) (s x)).width (t x)):=
  SplitMachineEmission.width (configWidth hn hs) (PhysicalSplitEmission.width hn) (initWork hn hs) (updateWork hn hs) ht
lemma current (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(PhysicalNode.machine (n x) (s x)).currentNet (t x)):=
  SplitMachineEmission.current (configWidth hn hs) (PhysicalSplitEmission.width hn) (initWork hn hs) (updateWork hn hs) ht
lemma initial (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(PhysicalNode.machine (n x) (s x)).initialNet (t x)):=
  SplitMachineEmission.initial (configWidth hn hs) (PhysicalSplitEmission.width hn) (initWork hn hs) (updateWork hn hs) ht
lemma program (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (ht : Emits ea unaryCode t) : OpsEmits ea (fun x=>(PhysicalNode.machine (n x) (s x)).program (t x)):=
  SplitMachineEmission.program (configWidth hn hs) (PhysicalSplitEmission.width hn) (PhysicalSplitEmission.initial hn) (PhysicalSplitEmission.program hn) (query hn hs) (update hn hs) ht
lemma start (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalNode.startNet (n x)):=by
  have hS:=((const _ _ 2).unaryMul hn).unarySucc
  have hz:=zeros hn (hS.unaryMul hn.unarySucc)
  exact ((stackPush hn hS hn.unarySucc (resize hn hn.unarySucc) hz).pair hz).pair (constant hn (const _ _ false))
lemma resultField (hn : Emits ea unaryCode n) (i : ∀x,Fin (n x))
    (hi : Emits ea Nat.bits (fun x=>(i x).val)) : NetEmits ea (fun x=>PhysicalNode.resultField (n x) (i x)):=
  ((NodeStateEmission.output ((const _ _ 2).unaryMul hn) hn.unarySucc).comp
    (blockNet ((const _ _ 2).unaryMul hn).unarySucc hn.unarySucc (fun x=>⟨(i x).val,by have:=(i x).isLt;omega⟩) hi)).comp (resize hn.unarySucc hn)
lemma sortedOutput (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalNode.sortedOutput (n x)):=by
  apply NetEmits.comp (g:=fun x=>BitArithmetic.SortedWords.sortNet (n x) (n x)) _ (SortingEmission.sort hn hn)
  apply tensor (configWidth hn ((const _ _ 2).unaryMul hn)) hn
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  exact resultField (hn.comp hx.snd) (fun x=>x.2) hx.fst.unaryNat
lemma kernelWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>NodeKernel.width (n x)):=
  width hn ((const _ _ 2).unaryMul hn) ((const _ _ 2).unaryMul hn)
lemma kernelInitial (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>NodeKernel.initialNet (n x)):=
  (start hn).comp (initial hn ((const _ _ 2).unaryMul hn) ((const _ _ 2).unaryMul hn))
lemma kernelProgram (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>NodeKernel.program (n x)):=
  program hn ((const _ _ 2).unaryMul hn) ((const _ _ 2).unaryMul hn)
end ExactQuantumFactoring.PhysicalNodeEmission

end



end OAI
