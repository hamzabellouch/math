import OAI.Analysis.IrrationalRotation.Model.VectorTraceState

namespace OAI

noncomputable section

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {ξ : H}

theorem IsFaithfulTracialVector.eq_zero_of_apply_eq_zero
    (h : IsFaithfulTracialVector M ξ) {A : H →L[ℂ] H}
    (hA : A ∈ M) (hξ : A ξ = 0) : A = 0 := by
  apply (CStarRing.star_mul_self_eq_zero_iff A).mp
  apply h.2.2 (star A * A) (mul_mem (star_mem hA) hA)
  · simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
      using ContinuousLinearMap.isPositive_adjoint_comp_self A
  · change inner ℂ ξ ((star A) (A ξ)) = 0
    simp [hξ]

theorem IsFaithfulTracialVector.eq_of_apply_eq
    (h : IsFaithfulTracialVector M ξ) {A B : H →L[ℂ] H}
    (hA : A ∈ M) (hB : B ∈ M) (hξ : A ξ = B ξ) : A = B := by
  apply sub_eq_zero.mp
  apply h.eq_zero_of_apply_eq_zero (sub_mem hA hB)
  change A ξ - B ξ = 0
  rw [hξ, sub_self]

theorem IsFaithfulTracialVector.injective_apply
    (h : IsFaithfulTracialVector M ξ) :
    Function.Injective (fun A : M => (A : H →L[ℂ] H) ξ) := by
  intro A B hAB
  exact Subtype.ext (h.eq_of_apply_eq A.property B.property hAB)

end Invariant233

end

end OAI
