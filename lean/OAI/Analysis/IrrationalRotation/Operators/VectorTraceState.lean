import OAI.Analysis.IrrationalRotation.Model.VectorTraceState

namespace OAI

noncomputable section

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
@[simp]
theorem vectorTraceCLM_apply (ξ : H) (A : H →L[ℂ] H) :
    vectorTraceCLM ξ A = vectorTrace ξ A := rfl

@[simp]
theorem vonNeumannVectorTraceCLM_apply (M : VonNeumannAlgebra H) (ξ : H) (A : M) :
    vonNeumannVectorTraceCLM M ξ A = vectorTrace ξ (A : H →L[ℂ] H) := rfl

@[simp]
theorem IsFaithfulTracialVector.toTracialState_apply {M : VonNeumannAlgebra H} {ξ : H}
    (h : IsFaithfulTracialVector M ξ) (A : M) :
    h.toTracialState A = vectorTrace ξ (A : H →L[ℂ] H) := rfl

theorem IsFaithfulTracialVector.toTracialState_faithful {M : VonNeumannAlgebra H} {ξ : H}
    (h : IsFaithfulTracialVector M ξ) (A : M)
    (hA : (A : H →L[ℂ] H).IsPositive) (hzero : h.toTracialState A = 0) : A = 0 := by
  apply Subtype.ext
  exact h.2.2 (A : H →L[ℂ] H) A.property hA hzero

end Invariant233

end

end OAI
