import Mathlib
import OAI.Analysis.HardSphere.Kernels.FiniteKernelPi

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {W I : Type*} [MeasurableSpace W] [Fintype I]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

lemma finiteKernelPi_finite (κ : ∀i,Kernel W (X i)) [∀i,IsFiniteKernel (κ i)] :
    IsFiniteKernel (finiteKernelPi κ) := inferInstance
instance finiteKernelPi_markov (κ : ∀i,Kernel W (X i)) [∀i,IsMarkovKernel (κ i)] :
    IsMarkovKernel (finiteKernelPi κ) := by
  constructor
  intro w
  rw [finiteKernelPi_apply]
  infer_instance

end HardSphere.Comparison

end
end

end

end OAI
