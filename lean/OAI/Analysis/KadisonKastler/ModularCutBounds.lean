import OAI.Analysis.KadisonKastler.GraphLowCutBound

namespace OAI

/-! # Quantitative modular cuts in every graph identification

The graph comparison controls three bounded spectral cuts. These estimates
are independent of the KMS condition and the Fourier gauge identity.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem modularUpperCut_high_inverse (J K : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : ℝ) :
    ∃ R : H →L[ℂ] H,
      ‖R‖ ≤ 1 + Real.exp (-(1 / 2 : ℝ)) ∧
      (1 - graphResolvent M K Ω (Real.exp (-a / 2))) * R =
        modularUpperCut M J Ω (a + 1 / 2) ∧
      modularUpperCut M J Ω (a + 1 / 2) * R = R := by
  rw [modularUpperCut_identification_independent J K]
  refine ⟨graphHighCutInverse M K Ω (Real.exp (-a / 2))
    (modularCutThreshold (a + 1 / 2)), ?_, ?_, ?_⟩
  · have hb := graphHighCutInverse_bound (M := M) K Ω (Real.exp_ne_zero (-a / 2))
      (modularCutThreshold_pos (a + 1 / 2)).le (modularCutThreshold_lt_one (a + 1 / 2))
    exact hb.trans_eq (graphHighInverse_bound_exp a)
  · exact graphHighCutInverse_identity K Ω (Real.exp_ne_zero _) (modularCutThreshold_lt_one _)
  · exact graphHighCutInverse_supported K Ω _ _

theorem modularUpperCut_low_bound (J K : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : ℝ) :
    ‖(1 - modularUpperCut M J Ω (a - 1 / 2)) *
      (1 - graphResolvent M K Ω (Real.exp (-a / 2)))‖ ≤
      Real.exp (-(1 / 2 : ℝ)) / (1 + Real.exp (-(1 / 2 : ℝ))) := by
  rw [modularUpperCut_identification_independent J K]
  exact (graphLowCut_bound K Ω (Real.exp_ne_zero _)
    (modularCutThreshold_pos _).le (modularCutThreshold_lt_one _).le).trans_eq
      (graphComplementScalar_exp a)

theorem modularUpperCut_low_support (J K : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : ℝ) :
    (1 - modularUpperCut M J Ω (a - 1 / 2)) *
      (1 - graphResolvent M K Ω (Real.exp (-a / 2))) *
      (1 - modularUpperCut M J Ω (a - 1 / 2)) =
    (1 - modularUpperCut M J Ω (a - 1 / 2)) *
      (1 - graphResolvent M K Ω (Real.exp (-a / 2))) := by
  rw [modularUpperCut_identification_independent J K]
  exact graphLowCut_support K Ω (Real.exp_ne_zero _) _

end

end KadisonKastler

end OAI
