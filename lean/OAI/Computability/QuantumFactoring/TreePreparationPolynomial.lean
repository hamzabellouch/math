import Mathlib
import OAI.Computability.QuantumFactoring.ChildQueueBounds
import OAI.Computability.QuantumFactoring.VerifiedTreeBounds
import OAI.Computability.QuantumFactoring.TreeQuarterPhysical
import OAI.Computability.QuantumFactoring.QuarterConstantResources
import OAI.Computability.QuantumFactoring.NodePreparationPolynomial

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace PreparationPolynomial
lemma treeConfig : PolyBound PhysicalTree.configWidth := by
  unfold PhysicalTree.configWidth PhysicalTree.capacity;poly_fast
lemma treeQuery_count (n : ℕ) : (PhysicalTree.query n).net.count=0 := by
  simp only [PhysicalTree.query,blockNet,count_select]
lemma treeQuery : NetworkPoly PhysicalTree.query := by
  simp only [NetworkPoly,treeQuery_count];exact PolyBound.const 0
lemma treePushed : NetworkPoly PhysicalTree.pushed := by
  apply PolyBound.of_le (g:=fun n=>PhysicalTree.capacity n*n*n+n*ChildQueue.oneBound
    (PhysicalTree.capacity n) n (PhysicalNode.resultBound n) n)
  · have cap : PolyBound PhysicalTree.capacity :=by unfold PhysicalTree.capacity;poly_fast
    have res : PolyBound PhysicalNode.resultBound :=
      (PolyBound.id.mul PolyBound.id).add ((PolyBound.id.mul PolyBound.id).mul
        (((PolyBound.const 498).mul PolyBound.id).add (PolyBound.const 114)))
    have lin : PolyBound (fun n=>2*PhysicalNode.resultBound n+96*n+25) :=
      (((PolyBound.const 2).mul res).add ((PolyBound.const 96).mul PolyBound.id)).add (PolyBound.const 25)
    have lin' : PolyBound (fun n=>PhysicalNode.resultBound n+159*n+6) :=
      (res.add ((PolyBound.const 159).mul PolyBound.id)).add (PolyBound.const 6)
    have one : PolyBound (fun n=>ChildQueue.oneBound (PhysicalTree.capacity n) n (PhysicalNode.resultBound n) n) :=
      (((((res.add ((PolyBound.const 49).mul PolyBound.id)).add (PolyBound.const 11)).add
        (PolyBound.id.mul lin)).add ((cap.mul PolyBound.id).mul lin')).add
          ((PolyBound.const 7).mul (cap.mul PolyBound.id)))
    exact ((cap.mul PolyBound.id).mul PolyBound.id).add (PolyBound.id.mul one)
  · intro n
    have h:=ChildQueue.pushAll_count (PhysicalTree.capacity n) (PhysicalTree.fields n)
      (c:=PhysicalNode.resultBound n) (by
        intro b hb
        obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hb
        simpa only [count_comp,tensorSelect,count_select,add_zero]
          using PhysicalTree.nodeResult_count n)
    have hs:=stackPop_count (PhysicalTree.capacity n) n
    have hh:=Nat.add_le_add hs h
    simpa only [PhysicalTree.pushed,PhysicalTree.localNode,PhysicalTree.old,
      count_comp,count_pair,count_select,ChildQueue.queue,
      zero_add,add_zero,PhysicalTree.fields,List.length_ofFn] using hh
lemma treeUpdate : NetworkPoly PhysicalTree.update := by
  apply PolyBound.of_le (g:=fun n=>97*n+21+7*PhysicalTree.configWidth n+(PhysicalTree.pushed n).net.count)
  · exact ((((PolyBound.const 97).mul PolyBound.id).add (PolyBound.const 21)).add
      ((PolyBound.const 7).mul treeConfig)).add treePushed
  · intro n
    have h:=zeroWord_count ((PhysicalTree.old n).comp (PhysicalTree.query n))
    simp only [count_comp,PhysicalTree.old,count_select,treeQuery_count,zero_add] at h
    simp only [PhysicalTree.update,wordMux_count,PhysicalTree.old,count_select]
    omega
lemma treeInitWork : PolyBound (fun n=>(PhysicalTree.machine n).initWork) :=
  treeQuery.add nodeInitial
lemma treeUpdateWork : PolyBound (fun n=>(PhysicalTree.machine n).updateWork) :=treeUpdate
lemma treeWidth : PolyBound PhysicalTree.width := by
  change PolyBound (fun n=>(PhysicalTree.machine n).width (PhysicalTree.steps n))
  simp only [NodeMachine.width_eq]
  have :=treeConfig;have :=nodeWidth;have :=treeInitWork;have :=treeUpdateWork
  unfold PhysicalTree.steps;poly_fast
lemma treeMachineInitial : PolyBound (fun n=>((PhysicalTree.machine n).initialNet
    (PhysicalTree.steps n)).net.count) := by
  simp only [NodeMachine.initialNet_count]
  have :=treeConfig;have :=nodeWidth;have :=treeInitWork;have :=treeUpdateWork
  unfold PhysicalTree.steps;poly_fast
lemma treeStart : NetworkPoly PhysicalTree.startNet := by
  apply PolyBound.of_le (g:=fun n=>PhysicalTree.capacity n*n*(PhysicalTree.capacity n*n))
  · unfold PhysicalTree.capacity;poly_fast
  · intro n
    simpa only [PhysicalTree.startNet,count_select,Completion.zeros_count,zero_add]
      using stackPush_count (select (n:=n) id) (Completion.zeros n (PhysicalTree.configWidth n))
lemma treeLaunchWork : PolyBound PhysicalTree.launchWork :=treeStart.comp treeMachineInitial
lemma treeSteps : PolyBound (fun n=>((PhysicalTree.machine n).program (PhysicalTree.steps n)).length) := by
  apply PolyBound.of_le (g:=fun n=>PhysicalTree.steps n*(4*(PhysicalTree.machine n).initWork+
    2*NodeKernel.width n+(NodeKernel.program n).length+
    4*(PhysicalTree.machine n).updateWork+2*PhysicalTree.configWidth n))
  · have :=treeInitWork;have :=nodeWidth;have :=nodeSteps;have :=treeUpdateWork;have :=treeConfig
    unfold PhysicalTree.steps;poly_fast
  · intro n;exact NodeMachine.program_length _ _
lemma treeLaunchWidth : PolyBound PhysicalTree.launchWidth :=by
  unfold PhysicalTree.launchWidth
  have :=treeWidth;have :=treeLaunchWork;poly_fast
lemma treeLaunchSteps : PolyBound (fun n=>(PhysicalTree.launchProgram n).length) := by
  apply PolyBound.of_le (g:=fun n=>4*PhysicalTree.launchWork n+2*PhysicalTree.width n+
    ((PhysicalTree.machine n).program (PhysicalTree.steps n)).length)
  · have :=treeLaunchWork;have :=treeWidth;have :=treeSteps;poly_fast
  · exact PhysicalTree.launchProgram_length
lemma treePadding : PolyBound PhysicalTree.padding := by
  apply (PolyBound.id.pow 10).of_le
  intro n;exact Nat.sub_le _ _
lemma treePaddedWidth : PolyBound PhysicalTree.paddedWidth :=by
  unfold PhysicalTree.paddedWidth
  simp only [tensorWidth_eq]
  exact treeLaunchWidth.add (treePadding.mul PolyBound.id)
lemma treePaddedSteps : PolyBound (fun n=>(PhysicalTree.paddedProgram n).length) :=by
  apply PolyBound.of_le (g:=fun n=>4*PhysicalTree.launchWork n+2*PhysicalTree.width n+
    ((PhysicalTree.machine n).program (PhysicalTree.steps n)).length+PhysicalTree.padding n*n)
  · have :=treeLaunchWork;have :=treeWidth;have :=treeSteps;have :=treePadding;poly_fast
  · exact PhysicalTree.paddedProgram_length
lemma quarterWidth : PolyBound PhysicalTree.quarterWidth :=by
  unfold PhysicalTree.quarterWidth
  exact (PolyBound.const 1).add (treePaddedWidth.add ((PolyBound.id.mul PolyBound.id).add Quarter.D_poly))
lemma quarterSteps : PolyBound (fun n=>(PhysicalTree.quarterProgram n).length) :=by
  simp only [PhysicalTree.quarterProgram_length]
  exact ((treePaddedSteps.add (PolyBound.const 1)).add (PolyBound.id.mul PolyBound.id)).add Quarter.D_poly
end PreparationPolynomial
end ExactQuantumFactoring

end



end OAI
