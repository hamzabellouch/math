import OAI.Analysis.KadisonKastler.StateOrbitMinimizer
import OAI.Analysis.KadisonKastler.StateOrbitNorm

namespace OAI

/-! # A singleton asymptotic hull inside every state-central orbit hull -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_singleton_stateOrbitCore
    (ξ : H) (hsep : Function.Injective (algebraVectorMap M ξ)) (a : Algebra M) :
    ∃ b : Algebra M, ContinuousLinearMapWOT.ofCLM b.val ∈ stateOrbitCore ξ a ∧
      stateOrbitCore ξ b = {ContinuousLinearMapWOT.ofCLM b.val} := by
  obtain ⟨B,hB,_,hmin⟩ := exists_unique_stateOrbitCore_minimizer ξ hsep a
  let b : Algebra M := ⟨B.toCLM,(stateOrbitCore_subset_ball ξ a hB).1⟩
  refine ⟨b,hB,?_⟩
  apply Set.Subset.antisymm
  · intro C hC
    apply Set.mem_singleton_iff.mpr
    exact hmin C (stateOrbitCore_compose_subset ξ a b hB hC)
      (stateOrbitCore_vector_norm_sq_le ξ b hC)
  · intro C hC
    rw [Set.mem_singleton_iff.mp hC]
    exact self_mem_stateOrbitCore ξ b

end

end KadisonKastler

end OAI
