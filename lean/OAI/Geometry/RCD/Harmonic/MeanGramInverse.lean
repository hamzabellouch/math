import OAI.Geometry.RCD.Coordinates.GramNormalization

namespace OAI

/-! # The actual inverse of an exactly normalized mean Gram -/

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  (U : E →L[ℝ] SobolevSpace μ hQ) (Ω : Set X) (hΩ : MeasurableSet Ω)
  (A : E ≃L[ℝ] E) (hA : IsExactMeanNormalization μ hQ U Ω hΩ A)

include hA

/-- Exact normalization makes the original mean Gram injective. -/
theorem meanGram_injective_of_exact_normalization :
    Function.Injective (sobolevMeanGram μ hQ U Ω hΩ) := by
  intro x y hxy
  by_contra hne
  have hp := meanGram_strictly_positive_of_exact_normalization μ hQ U Ω hΩ A hA
    (sub_ne_zero.mpr hne)
  rw [map_sub, hxy, sub_self, inner_zero_right] at hp
  exact (lt_irrefl 0) hp

/-- The mean Gram itself, with the inverse supplied by its proved
nondegeneracy. This is independent of which exact normalizer witnesses it. -/
def meanGramEquiv [FiniteDimensional ℝ E] : E ≃L[ℝ] E :=
  (LinearEquiv.ofInjectiveEndo (sobolevMeanGram μ hQ U Ω hΩ).toLinearMap
    (meanGram_injective_of_exact_normalization μ hQ U Ω hΩ A hA)).toContinuousLinearEquiv

@[simp] theorem meanGramEquiv_apply [FiniteDimensional ℝ E] (v : E) :
    meanGramEquiv μ hQ U Ω hΩ A hA v = sobolevMeanGram μ hQ U Ω hΩ v := rfl

/-- The inverse Gram direction is exactly `A A* xi`, without a symmetry
assumption on the chosen normalizer. -/
theorem meanGram_apply_normalizer_adjoint (xi : E) :
    sobolevMeanGram μ hQ U Ω hΩ (A (A.toContinuousLinearMap.adjoint xi)) = xi := by
  apply ext_inner_right ℝ
  intro z
  have h := congrArg (fun Q : E →L[ℝ] E =>
    ⟪A.symm z, Q (A.toContinuousLinearMap.adjoint xi)⟫_ℝ) hA
  rw [sobolevMeanGram_comp] at h
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearMap.id_apply, real_inner_comm] using h

@[simp] theorem meanGramEquiv_symm_apply [FiniteDimensional ℝ E] (xi : E) :
    (meanGramEquiv μ hQ U Ω hΩ A hA).symm xi = A (A.toContinuousLinearMap.adjoint xi) := by
  apply (meanGramEquiv μ hQ U Ω hΩ A hA).injective
  exact (meanGramEquiv μ hQ U Ω hΩ A hA).apply_symm_apply xi |>.trans
    (meanGram_apply_normalizer_adjoint μ hQ U Ω hΩ A hA xi).symm


end RegularPointCoordinates

end

end OAI
