import OAI.Combinatorics.ParityLifts.UniformBridge

namespace OAI

namespace ParityWL.Complexity

/-- Uniform exclusion under the weaker, single-machine subexponential
hypothesis; no positive forbidden rate and no convergence modulus are assumed. -/
theorem uniform_eth : UniformETHStatement := by
  intro hETH c i h
  obtain ⟨M,f,g,hlim,hm⟩ := h
  obtain ⟨d,hd⟩ := uniform_reduction c i M f g hlim hm
  exact hETH ⟨(raceCode (trialCode c M).decision).decision,d,hd⟩

end ParityWL.Complexity

end OAI
