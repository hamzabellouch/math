import OAI.Analysis.IrrationalRotation.Analysis.ConcretePredualCore

namespace OAI

noncomputable section
namespace Invariant233.ConcretePredual
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem continuous_vectorFunctional (M : VonNeumannAlgebra H) :
    Continuous (fun xy : H × H => vectorFunctional M xy.1 xy.2) := by
  exact (((innerSL ℂ).continuous.comp continuous_fst).clm_comp
    ((ContinuousLinearMap.apply ℂ H).continuous.comp continuous_snd)).clm_comp_const
      M.toSubalgebra.toSubmodule.subtypeL

theorem isSeparable_predual (M : VonNeumannAlgebra H)
    [TopologicalSpace.SeparableSpace H] :
    TopologicalSpace.IsSeparable (predual M : Set (StrongDual ℂ M)) := by
  exact ((TopologicalSpace.isSeparable_range (continuous_vectorFunctional M)).span).closure

instance separableSpace_predual (M : VonNeumannAlgebra H)
    [TopologicalSpace.SeparableSpace H] :
    TopologicalSpace.SeparableSpace (predual M) :=
  (isSeparable_predual M).separableSpace

end Invariant233.ConcretePredual

end

end OAI
