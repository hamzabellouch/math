import Mathlib.Algebra.BigOperators.Expect
import Mathlib.LinearAlgebra.Prod
import OAI.Computability.PerfectCompleteness.Algebra.BilinearGramCompressionLemmas
import OAI.Computability.PerfectCompleteness.Algebra.UniformLinearImage
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas

namespace OAI

section

namespace PerfectCompleteness.MatrixRowQuotientLaw

noncomputable section

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open MatrixRowQuotient

variable {𝕜 H K : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H] [AddCommGroup K] [Module 𝕜 K]

def projectMatrixLinear (W : Submodule 𝕜 H) :
    (Module.Dual 𝕜 H →ₗ[𝕜] K) →ₗ[𝕜] (Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K) where
  toFun := projectMatrix W
  map_add' X Y := by
    apply LinearMap.ext
    intro q
    rfl
  map_smul' a X := by
    apply LinearMap.ext
    intro q
    rfl

@[simp] theorem projectMatrixLinear_apply (W : Submodule 𝕜 H)
    (X : Module.Dual 𝕜 H →ₗ[𝕜] K) :
    projectMatrixLinear W X = projectMatrix W X := rfl

def jointProjection (W : Submodule 𝕜 H) :
    ((Module.Dual 𝕜 H →ₗ[𝕜] K) × H) →ₗ[𝕜]
      ((Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K) × (H ⧸ W)) :=
  (projectMatrixLinear W).prodMap W.mkQ

@[simp] theorem jointProjection_apply (W : Submodule 𝕜 H)
    (p : (Module.Dual 𝕜 H →ₗ[𝕜] K) × H) :
    jointProjection W p = (projectMatrix W p.1, W.mkQ p.2) := rfl

theorem jointProjection_surjective (W : Submodule 𝕜 H) :
    Function.Surjective (jointProjection (K := K) W) := by
  rintro ⟨X, h⟩
  obtain ⟨Y, hY⟩ := projectMatrix_surjective W X
  obtain ⟨g, hg⟩ := W.mkQ_surjective h
  exact ⟨(Y, g), Prod.ext hY hg⟩

theorem uniform_product {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    (FiniteDistribution.uniform A).product (FiniteDistribution.uniform B) =
      FiniteDistribution.uniform (A × B) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro p
  change (1 / (Fintype.card A : ℝ)) * (1 / (Fintype.card B : ℝ)) =
    1 / (Fintype.card (A × B) : ℝ)
  simp only [Fintype.card_prod, Nat.cast_mul, one_div, mul_inv]

variable (W : Submodule 𝕜 H)
  [Fintype H] [Fintype (H ⧸ W)]
  [Fintype (Module.Dual 𝕜 H →ₗ[𝕜] K)]
  [Fintype (Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K)]

theorem uniform_jointProjection :
    (FiniteDistribution.uniform ((Module.Dual 𝕜 H →ₗ[𝕜] K) × H)).pushforward
        (jointProjection W) =
      FiniteDistribution.uniform ((Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K) × (H ⧸ W)) :=
  UniformLinearImage.uniform_pushforward_linearMap
    (jointProjection W) (jointProjection_surjective W)

theorem independent_uniform_jointProjection :
    ((FiniteDistribution.uniform (Module.Dual 𝕜 H →ₗ[𝕜] K)).product
      (FiniteDistribution.uniform H)).pushforward (jointProjection W) =
    (FiniteDistribution.uniform (Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K)).product
      (FiniteDistribution.uniform (H ⧸ W)) := by
  rw [uniform_product, uniform_product]
  exact uniform_jointProjection W

private theorem expect_prod {A B : Type*} [Fintype A] [Fintype B]
    (f : A × B → ℝ) :
    (𝔼 p : A × B, f p) = 𝔼 a : A, 𝔼 b : B, f (a, b) := by
  simpa only [Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset A) (Finset.univ : Finset B) f

theorem expect_project_matrix_increment
    (f : (Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K) → (H ⧸ W) → ℝ) :
    (𝔼 X : Module.Dual 𝕜 H →ₗ[𝕜] K, 𝔼 h : H,
      f (projectMatrix W X) (W.mkQ h)) =
    𝔼 X : Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K, 𝔼 h : H ⧸ W, f X h := by
  have he := congrArg
    (fun μ : FiniteDistribution ((Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K) × (H ⧸ W)) =>
      μ.expectation (fun p => f p.1 p.2)) (uniform_jointProjection W)
  rw [FiniteDistribution.expectation_pushforward,
    FiniteDistribution.expectation_uniform, FiniteDistribution.expectation_uniform] at he
  have he' :
      (𝔼 p : (Module.Dual 𝕜 H →ₗ[𝕜] K) × H,
        f (projectMatrix W p.1) (W.mkQ p.2)) =
      𝔼 p : (Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K) × (H ⧸ W), f p.1 p.2 := by
    simpa only [Fintype.expect_eq_sum_div_card, jointProjection_apply] using he
  simpa only [expect_prod] using he'

theorem rankOne_pair_law (a : K) :
    ((FiniteDistribution.uniform (Module.Dual 𝕜 H →ₗ[𝕜] K)).product
      (FiniteDistribution.uniform H)).pushforward
        (fun p => (projectMatrix W p.1,
          projectMatrix W (p.1 + (Module.Dual.eval 𝕜 H p.2).smulRight a))) =
    ((FiniteDistribution.uniform (Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K)).product
      (FiniteDistribution.uniform (H ⧸ W))).pushforward
        (fun p => (p.1, p.1 + (Module.Dual.eval 𝕜 (H ⧸ W) p.2).smulRight a)) := by
  have he := congrArg
    (fun μ : FiniteDistribution ((Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K) × (H ⧸ W)) =>
      μ.pushforward (fun p =>
        (p.1, p.1 + (Module.Dual.eval 𝕜 (H ⧸ W) p.2).smulRight a)))
    (independent_uniform_jointProjection W)
  rw [FiniteDistribution.pushforward_comp] at he
  simpa only [jointProjection_apply, project_rankOne] using he

theorem expect_project_rankOne_pair (a : K)
    (f : (Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K) →
      (Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K) → ℝ) :
    (𝔼 X : Module.Dual 𝕜 H →ₗ[𝕜] K, 𝔼 h : H,
      f (projectMatrix W X)
        (projectMatrix W (X + (Module.Dual.eval 𝕜 H h).smulRight a))) =
    𝔼 X : Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K, 𝔼 h : H ⧸ W,
      f X (X + (Module.Dual.eval 𝕜 (H ⧸ W) h).smulRight a) := by
  simpa only [project_rankOne] using expect_project_matrix_increment W
    (fun X h => f X (X + (Module.Dual.eval 𝕜 (H ⧸ W) h).smulRight a))

end
end PerfectCompleteness.MatrixRowQuotientLaw

end

end OAI
