import OAI.Combinatorics.ContingencyTables.Counting.CountingPositiveSemantics
import OAI.Combinatorics.ContingencyTables.Transport.FiniteObservableTransport

namespace OAI

/-! # Flattening the positive run while preserving its complete output law -/
namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS CommonBasesFPRAS GridBoundary FiniteObservableTransport
open scoped Classical
noncomputable section

def independentOutput (req : Request)
    (words : Fin (phaseCount req)→Fin (phaseWidth req)→Bool) : TreeFraction.Fraction :=
  (CompanionOuterHistoryProgram.output
    (start (req,List.replicate (bitCount req) false),
      List.ofFn (fun i => List.ofFn (words i)))).2

theorem output_sameLaw (req : Request) :
    SameLaw (fun bits : Fin (bitCount req)→Bool => output (req,List.ofFn bits))
      (independentOutput req) := by
  intro phi
  have he := uniformAverage_equiv (gridWordEquiv (phaseCount req) (phaseWidth req))
    (fun words => phi (independentOutput req words))
  have hp : (fun bits : Fin (bitCount req)→Bool => phi (output (req,List.ofFn bits)))=
      (fun bits => phi (independentOutput req
        (gridWordEquiv (phaseCount req) (phaseWidth req) bits))) := by
    funext bits
    rw [output_ofFn,start_ofFn]
    rfl
  rw [hp]
  exact he

theorem value_sameLaw (req : Request) :
    SameLaw (fun bits : Fin (bitCount req)→Bool => TreeFraction.val (output (req,List.ofFn bits)))
      (fun words => TreeFraction.val (independentOutput req words)) :=
  (output_sameLaw req).map TreeFraction.val

end
end ContingencyTables.CountingPositiveProgram

end OAI
