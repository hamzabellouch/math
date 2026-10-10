import OAI.Analysis.KadisonKastler.FactorizationCyclicSpace

namespace OAI

/-! Compression of an operator factorization to its left generated space. -/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H}

def cyclicFactorRight (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L R : H →L[ℂ] K) : H →L[ℂ] factorizationCyclicSpace π L :=
  (factorizationCyclicSpace π L).orthogonalProjectionOnto.comp R

theorem cyclicFactorLeft_norm (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L : H →L[ℂ] K) : ‖cyclicFactorLeft π L‖ = ‖L‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
    intro ξ
    exact L.le_opNorm ξ
  · apply ContinuousLinearMap.opNorm_le_bound L (norm_nonneg (cyclicFactorLeft π L))
    intro ξ
    exact (cyclicFactorLeft π L).le_opNorm ξ

theorem cyclicFactorRight_norm_le (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L R : H →L[ℂ] K) : ‖cyclicFactorRight π L R‖ ≤ ‖R‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg R)
  intro ξ
  exact ((factorizationCyclicSpace π L).norm_orthogonalProjectionOnto_apply_le (R ξ)).trans
    (R.le_opNorm ξ)

theorem cyclicFactorization_eq (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L R : H →L[ℂ] K) (a : Algebra M) :
    (cyclicFactorLeft π L).adjoint.comp
        ((cyclicFactorRepresentation π L a).comp (cyclicFactorRight π L R)) =
      L.adjoint.comp ((π a).comp R) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro η
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ ((cyclicFactorRepresentation π L a).adjoint (cyclicFactorLeft π L η))
      ((factorizationCyclicSpace π L).orthogonalProjectionOnto (R ξ)) = _
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  have hstar : (((cyclicFactorRepresentation π L a).adjoint
      (cyclicFactorLeft π L η)) : K) = (π a).adjoint (L η) := by
    change ((star (cyclicFactorRepresentation π L a) (cyclicFactorLeft π L η)) : K) = _
    rw [← map_star]
    change π (star a) (L η) = _
    rw [map_star, ContinuousLinearMap.star_eq_adjoint]
  rw [hstar, ContinuousLinearMap.adjoint_inner_left]

theorem cyclicFactorRight_unique (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L : H →L[ℂ] K) (R S : H →L[ℂ] factorizationCyclicSpace π L)
    (h : ∀ a, (cyclicFactorLeft π L).adjoint.comp
      ((cyclicFactorRepresentation π L a).comp R) =
      (cyclicFactorLeft π L).adjoint.comp ((cyclicFactorRepresentation π L a).comp S)) :
    R = S := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply sub_eq_zero.mp
  apply factorizationCyclicSpace_total π L
  intro a η
  have he := congrArg (fun T : H →L[ℂ] H => inner ℂ η (T ξ)) (h (star a))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    map_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right] at he
  simpa only [inner_sub_right, sub_eq_zero] using he

end

end KadisonKastler

end OAI
