import OAI.Analysis.MarkovType.DyadicWeakMaxFromUpperL2
import OAI.Analysis.MarkovType.DyadicInterpolation

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finiteUpperL2_extrapolate_synthesis {r χ p : ℝ}
    (_hr : 1 < r) (hr2 : r ≤ 2) (hχ : 1 ≤ χ)
    (hUpper : FiniteUpperL2 E r χ) (hp : 1 < p) (hpr : p < r) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ (N : ℕ) (φ : DyadicAtom N → E),
      finiteMoment (dyadicLaw N).mass p (dyadicSynthesis N φ) ≤
        T ^ p * finiteMoment dyadicInputWeight p φ := by
  have hmax : ∀ a : ℝ, 1 < a → a < r →
      ∃ A : ℝ, 1 ≤ A ∧ DyadicNormalizedWeakMax E a A := by
    intro a ha har
    refine ⟨1 + (boundedEnergyConstant a r χ) ^ (2 : ℕ), ?_, ?_⟩
    · exact le_add_of_nonneg_right (sq_nonneg _)
    · exact finiteUpperL2_normalizedWeakMax ha har hr2 (zero_le_one.trans hχ) hUpper
  obtain ⟨K, hK, hstrong⟩ := dyadic_strong_of_normalizedWeakMax hp hpr hmax
  let T : ℝ := max 1 K
  have hT : 1 ≤ T := le_max_left _ _
  have hKT : K ≤ T ^ p :=
    (le_max_right 1 K).trans (Real.self_le_rpow_of_one_le hT hp.le)
  refine ⟨T, hT, ?_⟩
  intro N φ
  have hinput : 0 ≤ finiteMoment dyadicInputWeight p φ := by
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (dyadicInputWeight_nonneg i)
      (Real.rpow_nonneg (norm_nonneg (φ i)) p))
  exact (hstrong N φ).trans (mul_le_mul_of_nonneg_right hKT hinput)

theorem finiteUpperL2_extrapolate_dyadic {r χ p : ℝ}
    (hr : 1 < r) (hr2 : r ≤ 2) (hχ : 1 ≤ χ)
    (hUpper : FiniteUpperL2 E r χ) (hp : 1 < p) (hpr : p < r) :
    ∃ T : ℝ, 1 ≤ T ∧ FiniteDyadicUpperEstimate (X := E) p (T ^ p) (T ^ p) := by
  obtain ⟨T, hT, hstrong⟩ := finiteUpperL2_extrapolate_synthesis hr hr2 hχ hUpper hp hpr
  exact ⟨T, hT, finiteDyadicUpperEstimate_of_uniformStrong (zero_lt_one.trans hp) hstrong⟩

end MarkovSuperreflexivity

end

end OAI
