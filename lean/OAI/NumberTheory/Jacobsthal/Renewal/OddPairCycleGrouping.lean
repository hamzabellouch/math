import OAI.NumberTheory.Jacobsthal.Paths.PairBranchFullProjection

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.InitialRegeneration
open NumberTheoryLean.KernelPotential

noncomputable def pairWindowContinue (v H : ℝ) : Kernel OddCost OddCost :=
  pairBranchKernel false+pairBranchKernel true ∘ₖ stateFilter (ordinaryCostWindow_measurable v H).compl

instance pairWindowContinue_isFiniteKernel (v H : ℝ) : IsFiniteKernel (pairWindowContinue v H) := by
  unfold pairWindowContinue
  infer_instance

lemma pairWindowContinue_complete (v H : ℝ) :
    hitOrReturn ∘ₖ pairWindowContinue v H=ordinaryWindowContinue v H := by
  rw [pairWindowContinue,Kernel.comp_add_right,← Kernel.comp_assoc,
    ← cycleBranch_completion false,← cycleBranch_completion true]
  rfl

noncomputable def oddConsecutiveCapture (v H : ℝ) : Kernel OddCost OddCost :=
  ordinaryWindowCapture v H ∘ₖ regenerationInput

noncomputable def oddConsecutiveContinue (v H : ℝ) : Kernel OddCost OddCost :=
  pairedCostKernel ∘ₖ nonregenerationInput+pairWindowContinue v H ∘ₖ regenerationInput

instance oddConsecutiveCapture_isFiniteKernel (v H : ℝ) : IsFiniteKernel (oddConsecutiveCapture v H) := by
  unfold oddConsecutiveCapture
  infer_instance

instance oddConsecutiveContinue_isFiniteKernel (v H : ℝ) : IsFiniteKernel (oddConsecutiveContinue v H) := by
  unfold oddConsecutiveContinue
  infer_instance

noncomputable def oddConsecutiveHit (v H : ℝ) : Kernel OddCost OddCost :=
  potential (oddConsecutiveCapture v H) (oddConsecutiveContinue v H)

theorem oddConsecutiveHit_eq_cycles (v H : ℝ) :
    oddConsecutiveHit v H=ordinaryMarkedHit v H ∘ₖ hitOrReturn := by
  rw [oddConsecutiveHit,oddConsecutiveContinue,first_capture_decomposition,
    oddConsecutiveCapture,
    potential_comp_left regenerationInput (ordinaryWindowCapture v H) (pairedCostKernel ∘ₖ nonregenerationInput),
    potential_comp_left regenerationInput (pairWindowContinue v H) (pairedCostKernel ∘ₖ nonregenerationInput),
    ← hitOrReturn_eq_input_potential,potential_exchange,pairWindowContinue_complete]
  rfl

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
