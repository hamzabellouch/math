import OAI.Analysis.KadisonSimilarity.Tracial.ConcreteProjectionComparison

namespace OAI

/-! Projection comparison is transported through the trace-preserving
normal-model coordinates used in the finite-factor application. -/

noncomputable section
namespace KadisonSimilarity

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem finiteFactorProjectionComparison_of_equiv (e : A ≃⋆ₐ[ℂ] B)
    (τA : A → ℝ) (τB : B → ℝ) (hτ : ∀ a, τB (e a) = τA a)
    (comparison : FiniteFactorProjectionComparison τB) :
    FiniteFactorProjectionComparison τA := by
  intro p q hp hq hpq
  obtain ⟨v, hv, hpv⟩ := comparison (e p) (e q) (hp.map e) (hq.map e)
    (by simpa only [hτ] using hpq)
  refine ⟨e.symm v, ?_, ?_⟩
  · have h := congrArg e.symm hv
    simpa only [map_mul, map_star, e.symm_apply_apply] using h
  · have h := congrArg e.symm hpv
    simpa only [map_mul, map_star, e.symm_apply_apply] using h

end KadisonSimilarity

end

end OAI
