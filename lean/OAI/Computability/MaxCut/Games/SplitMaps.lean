import Mathlib
import OAI.Computability.MaxCut.Games.RowErasureSliceQuotient

namespace OAI

/-! Actual splitting of linear-map questions and their uniform laws. -/

noncomputable section

open scoped BigOperators

namespace MaxCutGames.Fourier.SplitMaps

variable {K E C D : Type*} [CommSemiring K]
    [AddCommMonoid E] [Module K E]
    [AddCommMonoid C] [Module K C]
    [AddCommMonoid D] [Module K D]

/-- A question into the symbol/perpendicular product is exactly a pair of
independent coordinate questions. -/
def codomainSplit : (E →ₗ[K] C × D) ≃ₗ[K] (E →ₗ[K] C) × (E →ₗ[K] D) :=
  (LinearMap.prodEquiv K).symm

/-- A dual Fourier index on a product is exactly its two restrictions. -/
def domainSplit : (C × D →ₗ[K] E) ≃ₗ[K] (C →ₗ[K] E) × (D →ₗ[K] E) :=
  (LinearMap.coprodEquiv K).symm

@[simp] theorem codomainSplit_symm_apply (X : E →ₗ[K] C) (Z : E →ₗ[K] D) :
    codomainSplit.symm (X, Z) = X.prod Z := rfl

@[simp] theorem domainSplit_symm_apply (S : C →ₗ[K] E) (T : D →ₗ[K] E) :
    domainSplit.symm (S, T) = S.coprod T := rfl

theorem expect_codomain_product
    [Fintype (E →ₗ[K] C × D)] [Fintype (E →ₗ[K] C)] [Fintype (E →ₗ[K] D)]
    {A : Type*} [AddCommMonoid A] [Module ℚ≥0 A]
    (f : (E →ₗ[K] C × D) → A) :
    (𝔼 X, f X) = 𝔼 (X : E →ₗ[K] C), 𝔼 (Z : E →ₗ[K] D), f (X.prod Z) := by
  classical
  rw [Fintype.expect_equiv codomainSplit.toEquiv f
    (fun p => f (p.1.prod p.2)) (by intro X; rfl)]
  rw [← Finset.univ_product_univ, Finset.expect_product]

theorem expect_domain_product
    [Fintype (C × D →ₗ[K] E)] [Fintype (C →ₗ[K] E)] [Fintype (D →ₗ[K] E)]
    {A : Type*} [AddCommMonoid A] [Module ℚ≥0 A]
    (f : (C × D →ₗ[K] E) → A) :
    (𝔼 S, f S) = 𝔼 (S : C →ₗ[K] E), 𝔼 (T : D →ₗ[K] E), f (S.coprod T) := by
  classical
  rw [Fintype.expect_equiv domainSplit.toEquiv f
    (fun p => f (p.1.coprod p.2)) (by
      intro S
      simp [domainSplit])]
  rw [← Finset.univ_product_univ, Finset.expect_product]

theorem sum_domain_product
    [Fintype (C × D →ₗ[K] E)] [Fintype (C →ₗ[K] E)] [Fintype (D →ₗ[K] E)]
    {A : Type*} [AddCommMonoid A]
    (f : (C × D →ₗ[K] E) → A) :
    (∑ S, f S) = ∑ (S : C →ₗ[K] E), ∑ (T : D →ₗ[K] E), f (S.coprod T) := by
  classical
  rw [← domainSplit.symm.toEquiv.sum_comp f]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  rfl

end MaxCutGames.Fourier.SplitMaps
end

end OAI
