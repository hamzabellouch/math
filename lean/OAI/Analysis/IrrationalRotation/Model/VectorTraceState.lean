import OAI.Analysis.IrrationalRotation.Model.OperatorProperties
import OAI.Analysis.IrrationalRotation.Model.Spectral

namespace OAI

noncomputable section

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance vonNeumannSMulMemClass :
    SMulMemClass (VonNeumannAlgebra H) ℂ (H →L[ℂ] H) where
  smul_mem {s} c {_} ha := s.toSubalgebra.smul_mem ha c

instance vonNeumannNormClosed (M : VonNeumannAlgebra H) :
    IsClosed (M : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  rw [← M.centralizer_centralizer']
  exact Set.isClosed_centralizer _

def vectorTraceCLM (ξ : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ ξ).comp ((ContinuousLinearMap.apply ℂ H) ξ)

def vonNeumannVectorTraceCLM (M : VonNeumannAlgebra H) (ξ : H) : M →L[ℂ] ℂ :=
  (vectorTraceCLM ξ).comp M.toSubalgebra.toSubmodule.subtypeL

def IsFaithfulTracialVector.toTracialState {M : VonNeumannAlgebra H} {ξ : H}
    (h : IsFaithfulTracialVector M ξ) : TracialState M where
  toContinuousLinearMap := vonNeumannVectorTraceCLM M ξ
  map_one := by
    change inner ℂ ξ ξ = 1
    rw [inner_self_eq_norm_sq_to_K, h.1]
    norm_num
  map_star := by
    intro a
    change inner ℂ ξ ((star (a : H →L[ℂ] H)) ξ) =
      star (inner ℂ ξ ((a : H →L[ℂ] H) ξ))
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    exact (inner_conj_symm _ _).symm
  positive := by
    intro a
    change 0 ≤ (inner ℂ ξ ((star (a : H →L[ℂ] H)) ((a : H →L[ℂ] H) ξ))).re
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_nonneg (𝕜 := ℂ) (x := (a : H →L[ℂ] H) ξ)
  tracial := by
    intro a b
    exact h.2.1 (a : H →L[ℂ] H) (b : H →L[ℂ] H) a.property b.property

end Invariant233

end

end OAI
