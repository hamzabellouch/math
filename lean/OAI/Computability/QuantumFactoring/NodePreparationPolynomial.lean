import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalNodeKernel
import OAI.Computability.QuantumFactoring.NetworkPoly
import OAI.Computability.QuantumFactoring.ActualDivisorPolynomial
import OAI.Computability.QuantumFactoring.PrimalityPolynomial

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace PreparationPolynomial
lemma nodeConfig : PolyBound (fun n=>PhysicalNode.configWidth n (2*n)) := by
  unfold PhysicalNode.configWidth NodeStateCircuit.width
  poly_fast
lemma nodeQuery : NetworkPoly (fun n=>PhysicalNode.query n (2*n)) := by
  apply PolyBound.id.of_le
  intro n
  simpa only [PhysicalNode.query,count_comp,NodeStateCircuit.top_count,zero_add]
    using resizeWord_count (n+1) n
lemma nodeStep : NetworkPoly (fun n=>NodeStateCircuit.step (2*n) (n+1)) := by
  apply PolyBound.of_le (g:=fun n=>NodeStateCircuit.stepBound (2*n) (n+1))
  · exact nodeStepBound_poly ((PolyAt.const id 2).mul (PolyAt.self id))
      ((PolyAt.self id).add (PolyAt.const id 1))
  · intro n;exact NodeStateCircuit.step_count _ _
lemma nodeUpdate : NetworkPoly (fun n=>PhysicalNode.update n (2*n)) :=
  ((NetworkPoly.select _).pair ((NetworkPoly.select _).comp FixedSplit.divisorNet_poly)).comp nodeStep
lemma nodeInitWork : PolyBound (fun n=>(PhysicalNode.machine n (2*n)).initWork) :=
  nodeQuery.add splitInitial
lemma nodeUpdateWork : PolyBound (fun n=>(PhysicalNode.machine n (2*n)).updateWork) := nodeUpdate
lemma nodeWidth : PolyBound NodeKernel.width := by
  change PolyBound (fun n=>(PhysicalNode.machine n (2*n)).width (2*n))
  simp only [SplitMachine.width_eq]
  have :=nodeConfig;have:=splitWidth;have:=nodeInitWork;have:=nodeUpdateWork
  poly_fast
lemma machineNodeInitial : PolyBound (fun n=>((PhysicalNode.machine n (2*n)).initialNet (2*n)).net.count) := by
  simp only [SplitMachine.initialNet_count]
  have :=nodeConfig;have:=splitWidth;have:=nodeInitWork;have:=nodeUpdateWork
  poly_fast
lemma nodeStart : NetworkPoly PhysicalNode.startNet := by
  apply PolyBound.of_le (g:=fun n=>(2*n+1)*(n+1)*((n+1)+(2*n+1)*(n+1))+(2*n+1)*(n+1)+1)
  · poly_fast
  · intro n
    have hh:=stackPush_count (resizeWord n (n+1)) (Completion.zeros n ((2*n+1)*(n+1)))
    simp only [Completion.zeros_count] at hh
    have hr:=resizeWord_count n (n+1)
    have hh' :=hh.trans (Nat.mul_le_mul_left ((2*n+1)*(n+1)) (Nat.add_le_add_right hr _))
    simp only [PhysicalNode.startNet,count_pair,Completion.zeros_count,count_constant]
    omega
lemma nodeInitial : NetworkPoly NodeKernel.initialNet := nodeStart.comp machineNodeInitial
lemma nodeSteps : PolyBound (fun n=>(NodeKernel.program n).length) := by
  apply PolyBound.of_le (g:=fun n=>2*n*(4*(PhysicalNode.machine n (2*n)).initWork+
    2*FixedSplit.width n+(FixedSplit.program n).length+
    4*(PhysicalNode.machine n (2*n)).updateWork+2*PhysicalNode.configWidth n (2*n)))
  · have :=nodeInitWork;have:=splitWidth;have:=splitSteps;have:=nodeUpdateWork;have:=nodeConfig
    poly_fast
  · intro n;exact SplitMachine.program_length _ _
end PreparationPolynomial
end ExactQuantumFactoring

end



end OAI
