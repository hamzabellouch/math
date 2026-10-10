import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalSplitLaunch
import OAI.Computability.QuantumFactoring.PolyBounds

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
syntax "poly_fast" : tactic
macro_rules
  | `(tactic| poly_fast) => `(tactic|
    with_reducible_and_instances first
    | assumption
    | exact PolyBound.id
    | exact PolyBound.const _
    | (apply PolyBound.add <;> poly_fast)
    | (apply PolyBound.mul <;> poly_fast)
    | (apply PolyBound.pow <;> poly_fast)
    | (apply PolyBound.max <;> poly_fast)
    | (apply PolyBound.sub <;> poly_fast)
    | (apply PolyBound.div <;> poly_fast)
    | (apply PolyBound.mod <;> poly_fast)
    | (apply PolyBound.natSize <;> poly_fast))
namespace PreparationPolynomial

lemma sampleExponent : PolyBound OrderSlots.sampleExponent := by
  unfold OrderSlots.sampleExponent; poly_fast
lemma retentionBits : PolyBound OrderTrial.retentionBits := by
  unfold OrderTrial.retentionBits; poly_fast
lemma transitionWidth : PolyBound Completion.transitionWidth := by
  unfold Completion.transitionWidth; poly_fast
lemma samplerWork : PolyBound ListSampler.work := by
  unfold ListSampler.work; poly_fast
lemma samplerWidth : PolyBound ListSampler.width := by
  change PolyBound (fun n=>n+n+(n+ListSampler.work n))
  have := samplerWork; poly_fast
lemma sampleScratch : PolyBound (fun n=>OrderSample.scratch n (OrderSlots.sampleExponent n+2)) := by
  unfold OrderSample.scratch
  have := sampleExponent; poly_fast
lemma sampleWidth : PolyBound (fun n=>OrderSample.width n (OrderSlots.sampleExponent n+2)) := by
  unfold OrderSample.width OrderSample.inputWidth
  have := sampleExponent; have := sampleScratch; poly_fast
lemma rawWidth : PolyBound (fun n=>OrderTrial.rawWidth n (OrderSlots.sampleExponent n) n) := by
  unfold OrderTrial.rawWidth OrderTrial.guessWidth
  have := sampleWidth; have := retentionBits; poly_fast
lemma listCoin : PolyBound (fun n=>Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5)) := by
  unfold Completion.coinBits
  have := transitionWidth; poly_fast
lemma orderCoin : PolyBound OrderSlots.coinWidth := by
  unfold OrderSlots.coinWidth Completion.coinBits
  have := transitionWidth; poly_fast
lemma listWidth : PolyBound PhysicalListSlots.width := by
  unfold PhysicalListSlots.width PhysicalListSlots.ordinaryWidth
  simp only [tensorWidth_eq]
  have := samplerWidth; have := transitionWidth; have := listCoin; poly_fast
lemma orderWidth : PolyBound OrderSlots.width := by
  unfold OrderSlots.width OrderSlots.ordinaryWidth
  simp only [tensorWidth_eq]
  have := rawWidth; have := transitionWidth; have := orderCoin; poly_fast
lemma listOutput : PolyBound (fun n=>(PhysicalListSlots.outputNet n).net.count) := by
  apply PolyBound.of_le (g:=fun n=>8*Completion.transitionWidth n+194*n+21)
  · have := transitionWidth; poly_fast
  · exact PhysicalListSlots.outputNet_count
lemma listWork : PolyBound PhysicalListSlots.work := by
  apply PolyBound.of_le (g:=fun n=>n^5*ListSampler.width n+2*n+Completion.transitionWidth n+
      Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5))
  · have := samplerWidth;have := transitionWidth;have:=listCoin;poly_fast
  · exact PhysicalListSlots.initialNet_count
lemma orderWork : PolyBound (fun n=>(OrderSlots.initialNet n).net.count) := by
  apply PolyBound.of_le (g:=fun n=>n^5*OrderTrial.rawWidth n (OrderSlots.sampleExponent n) n+
      2*n+Completion.transitionWidth n+OrderSlots.coinWidth n)
  · have := rawWidth;have:=transitionWidth;have:=orderCoin;poly_fast
  · exact OrderSlots.initialNet_count
lemma listSteps : PolyBound (fun n=>(PhysicalListSlots.program n).length) := by
  apply PolyBound.of_le (g:=fun n=>n^5*(4*ListSampler.work n+3*n)+2*n+Completion.transitionWidth n+
      Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5))
  · have:=samplerWork;have:=transitionWidth;have:=listCoin;poly_fast
  · exact PhysicalListSlots.program_length
lemma orderSteps : PolyBound (fun n=>(OrderSlots.program n).length) := by
  apply PolyBound.of_le (g:=fun n=>n^5*(2+((OrderSlots.sampleExponent n+2)+
      4*OrderSample.scratch n (OrderSlots.sampleExponent n+2)+2*n+
      (OrderSlots.sampleExponent n+2)*(998*(OrderSlots.sampleExponent n+2)+49)+
      2*(OrderSlots.sampleExponent n+5))+3*n+OrderTrial.retentionBits n)+2*n+
      Completion.transitionWidth n+OrderSlots.coinWidth n)
  · have:=sampleExponent;have:=sampleScratch;have:=retentionBits
    have:=transitionWidth;have:=orderCoin;poly_fast
  · exact OrderSlots.program_length
lemma listLaunchWidth : PolyBound PhysicalListSlots.launchWidth := by
  unfold PhysicalListSlots.launchWidth
  have:=listWidth;have:=listWork;poly_fast
lemma listLaunchSteps : PolyBound (fun n=>(PhysicalListSlots.launch n).length) := by
  apply PolyBound.of_le (g:=fun n=>4*PhysicalListSlots.work n+2*PhysicalListSlots.width n+
      (PhysicalListSlots.program n).length)
  · have:=listWork;have:=listWidth;have:=listSteps;poly_fast
  · exact PhysicalListSlots.launch_length
lemma splitWork : PolyBound FixedSplit.work := by
  change PolyBound (fun n=>(FixedSplit.ordersInitialNet n).net.count)
  simp only [FixedSplit.ordersInitialNet_count]
  have:=listOutput;have:=orderWork;poly_fast
lemma ordersWidth : PolyBound FixedSplit.ordersWidth := by
  unfold FixedSplit.ordersWidth
  simp only [tensorWidth_eq]
  have:=orderWidth;poly_fast
lemma splitWidth : PolyBound FixedSplit.width := by
  unfold FixedSplit.width
  have:=listLaunchWidth;have:=ordersWidth;have:=splitWork;poly_fast
lemma splitSteps : PolyBound (fun n=>(FixedSplit.program n).length) := by
  apply PolyBound.of_le (g:=fun n=>(PhysicalListSlots.launch n).length+4*FixedSplit.work n+
      2*FixedSplit.ordersWidth n+n^5*(OrderSlots.program n).length)
  · have:=listLaunchSteps;have:=splitWork;have:=ordersWidth;have:=orderSteps;poly_fast
  · exact FixedSplit.program_length
lemma splitInitial : PolyBound (fun n=>(FixedSplit.initialNet n).net.count) := by
  simp only [FixedSplit.initialNet_count]
  have:=listWidth;have:=listWork;have:=ordersWidth;have:=splitWork;poly_fast

end PreparationPolynomial
end ExactQuantumFactoring

end



end OAI
