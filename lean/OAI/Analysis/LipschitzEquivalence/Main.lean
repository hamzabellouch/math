import OAI.Analysis.LipschitzEquivalence.CompactHilbertWSC

namespace OAI

noncomputable section
namespace LipschitzCounterexample

theorem main : MainClaim :=
  SeparatingStages.main_of_free_wsc CompactWSC.hilbert_free_wsc

end LipschitzCounterexample

end

end OAI
