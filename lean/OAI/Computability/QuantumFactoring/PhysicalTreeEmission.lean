import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalNodeEmission
import OAI.Computability.QuantumFactoring.ChildQueueEmission
import OAI.Computability.QuantumFactoring.NodeMachineEmission

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
lemma capacity (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.capacity (n x)):=
  ((const _ _ 2).unaryMul (hn.unaryPow 2)).unarySucc
lemma configWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.configWidth (n x)):=(capacity hn).unaryMul hn
lemma query (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.query (n x)):=
  blockNet (capacity hn) hn (fun _=>0) (const _ _ 0)
lemma nodeResult (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.nodeResult (n x)):=
  (PhysicalNodeEmission.current hn ((const _ _ 2).unaryMul hn) ((const _ _ 2).unaryMul hn)).comp
    (PhysicalNodeEmission.sortedOutput hn)
lemma fields (hn : Emits ea unaryCode n) : NetEmits
    (fun x:Σa,Fin (n a)=>prodCode unaryCode ea (x.2.val,x.1))
    (fun x=>(PhysicalTree.nodeResult (n x.1)).comp (ExactQuantumFactoring.tensorSelect (n x.1) (n x.1) x.2)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin (n a)=>(x.2.val,x.1))
  have hN:=hn.comp hx.snd
  exact (nodeResult hN).comp (NetEmits.tensorSelect hN hN (fun x=>x.2) hx.fst.unaryNat)
lemma old (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.old (n x)):=
  left (configWidth hn) (PhysicalNodeEmission.kernelWidth hn)
lemma localNode (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.localNode (n x)):=
  right (configWidth hn) (PhysicalNodeEmission.kernelWidth hn)
lemma pushed (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.pushed (n x)):=
  (((localNode hn).pair ((old hn).comp (stackPop (capacity hn) hn))).comp
    (childPushAll (PhysicalNodeEmission.kernelWidth hn) hn hn (capacity hn) (fields hn))).comp
      (right (PhysicalNodeEmission.kernelWidth hn) (configWidth hn))
lemma update (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.update (n x)):=
  (zeroWord ((configWidth hn).unaryAdd (PhysicalNodeEmission.kernelWidth hn)) hn ((old hn).comp (query hn))).wordMux (old hn) (pushed hn) (configWidth hn)
lemma initWork (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>(PhysicalTree.machine (n x)).initWork):=
  (query hn).count.unaryAdd (PhysicalNodeEmission.kernelInitial hn).count
lemma updateWork (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>(PhysicalTree.machine (n x)).updateWork):=(update hn).count
lemma machineWidth (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : Emits ea unaryCode (fun x=>(PhysicalTree.machine (n x)).width (t x)):=
  NodeMachineEmission.width (configWidth hn) (PhysicalNodeEmission.kernelWidth hn) (initWork hn) (updateWork hn) ht
lemma machineInitial (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : NetEmits ea (fun x=>(PhysicalTree.machine (n x)).initialNet (t x)):=
  NodeMachineEmission.initial (configWidth hn) (PhysicalNodeEmission.kernelWidth hn) (initWork hn) (updateWork hn) ht
lemma machineProgram (hn : Emits ea unaryCode n) (ht : Emits ea unaryCode t) : OpsEmits ea (fun x=>(PhysicalTree.machine (n x)).program (t x)):=
  NodeMachineEmission.program (configWidth hn) (PhysicalNodeEmission.kernelWidth hn) (PhysicalNodeEmission.kernelInitial hn)
    (PhysicalNodeEmission.kernelProgram hn) (query hn) (update hn) ht
lemma start (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.startNet (n x)):=
  stackPush hn (capacity hn) hn (identity hn) (zeros hn (configWidth hn))
lemma steps (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.steps (n x)):=(const _ _ 2).unaryMul (hn.unaryPow 2)
lemma width (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>PhysicalTree.width (n x)):=machineWidth hn (steps hn)
lemma initial (hn : Emits ea unaryCode n) : NetEmits ea (fun x=>PhysicalTree.initialNet (n x)):=(start hn).comp (machineInitial hn (steps hn))
lemma program (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>(PhysicalTree.machine (n x)).program (PhysicalTree.steps (n x))):=machineProgram hn (steps hn)
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
