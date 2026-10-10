import Mathlib
import OAI.Analysis.Commutator.NormalPredual
import OAI.Analysis.Commutator.ProjectionNormalStrong

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def strongFunctional (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) : StrongDual ℂ M where
  toLinearMap := f.toLinearMap
  cont := map_continuous f

theorem mem_predual [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) (hf : ProjectionContinuousAtOne M f) :
    strongFunctional M f∈closure (NormalPredual.finiteTests M (TopologicalSpace.denseSeq H)) := by
  apply NormalPredual.mem_closure_of_strong_null M (TopologicalSpace.denseSeq H)
    (TopologicalSpace.denseRange_denseSeq H)
  intro T hT ht
  exact contraction_strong_null M f hf T hT ht

theorem boundedWOTContinuous [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) (hf : ProjectionContinuousAtOne M f) :
    NormalPredual.BoundedWOTContinuous M (strongFunctional M f) :=
  NormalPredual.normal_of_mem_closure M (TopologicalSpace.denseSeq H) (mem_predual M f hf)

end Kadison.PositiveWOT

end

end
end

end OAI
