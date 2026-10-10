import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Basic.Real.Basic
import OAI.Computability.PerfectCompleteness.Foundations.DummyEliminationLemmas
import OAI.Computability.PerfectCompleteness.Reduction.CompletionSoundness
import OAI.Computability.PerfectCompleteness.Sampling.DensityVariation

namespace OAI


namespace PerfectCompleteness.CommonProductVariation

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {S A Γ : Type*} [Fintype S] [Fintype A] [Fintype Γ]

theorem product_totalVariation (μ : FiniteDistribution S)
    (P Q : FiniteDistribution A) :
    (μ.product P).totalVariation (μ.product Q) = P.totalVariation Q := by
  change (∑ z : S × A,
    |μ.weight z.1 * P.weight z.2 - μ.weight z.1 * Q.weight z.2|) / 2 =
      (∑ a : A, |P.weight a - Q.weight a|) / 2
  rw [Fintype.sum_prod_type]
  simp_rw [← mul_sub, abs_mul, abs_of_nonneg (μ.nonnegative _), ← Finset.mul_sum]
  rw [← Finset.sum_mul, μ.normalized, one_mul]

theorem observed_product_le (μ : FiniteDistribution S)
    (P Q : FiniteDistribution A) (observe : S × A → Γ) :
    ((μ.product P).pushforward observe).totalVariation
      ((μ.product Q).pushforward observe) ≤ P.totalVariation Q :=
  (DensityVariation.variation_pushforward_le _ _ observe).trans_eq
    (product_totalVariation μ P Q)

theorem observed_product_le_of_bound (μ : FiniteDistribution S)
    (P Q : FiniteDistribution A) (observe : S × A → Γ)
    {error : ℝ} (herror : P.totalVariation Q ≤ error) :
    ((μ.product P).pushforward observe).totalVariation
      ((μ.product Q).pushforward observe) ≤ error :=
  (observed_product_le μ P Q observe).trans herror

end
end PerfectCompleteness.CommonProductVariation


namespace PerfectCompleteness.ConditionalVariation

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open CompletionSoundness

noncomputable section

variable {S : Type*} [Fintype S] {Ω : S → Type*} [∀ s, Fintype (Ω s)]

theorem sigma_totalVariation (μ : FiniteDistribution S)
    (P Q : (s : S) → FiniteDistribution (Ω s)) :
    (sigmaLaw μ P).totalVariation (sigmaLaw μ Q) =
      μ.expectation (fun s => (P s).totalVariation (Q s)) := by
  change (∑ z : Σ s, Ω s,
    |μ.weight z.1 * (P z.1).weight z.2 - μ.weight z.1 * (Q z.1).weight z.2|) / 2 =
      ∑ s, μ.weight s * ((∑ x : Ω s, |(P s).weight x - (Q s).weight x|) / 2)
  rw [Fintype.sum_sigma, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [← mul_sub, abs_mul, abs_of_nonneg (μ.nonnegative s)]
  rw [← Finset.mul_sum]
  simp only [div_eq_mul_inv, mul_assoc]

theorem observed_sigma_le {Γ : Type*} [Fintype Γ]
    (μ : FiniteDistribution S) (P Q : (s : S) → FiniteDistribution (Ω s))
    (observe : (Σ s, Ω s) → Γ) :
    ((sigmaLaw μ P).pushforward observe).totalVariation
      ((sigmaLaw μ Q).pushforward observe) ≤
        μ.expectation (fun s => (P s).totalVariation (Q s)) := by
  rw [← sigma_totalVariation μ P Q]
  exact DensityVariation.variation_pushforward_le _ _ observe

theorem observed_sigma_le_of_bound {Γ : Type*} [Fintype Γ]
    (μ : FiniteDistribution S) (P Q : (s : S) → FiniteDistribution (Ω s))
    (error : S → ℝ) (bound : ∀ s, (P s).totalVariation (Q s) ≤ error s)
    (observe : (Σ s, Ω s) → Γ) :
    ((sigmaLaw μ P).pushforward observe).totalVariation
      ((sigmaLaw μ Q).pushforward observe) ≤ μ.expectation error :=
  (observed_sigma_le μ P Q observe).trans (SmallBias.expectation_mono μ bound)

theorem observed_sigma_le_const {Γ : Type*} [Fintype Γ]
    (μ : FiniteDistribution S) (P Q : (s : S) → FiniteDistribution (Ω s))
    (error : ℝ) (bound : ∀ s, (P s).totalVariation (Q s) ≤ error)
    (observe : (Σ s, Ω s) → Γ) :
    ((sigmaLaw μ P).pushforward observe).totalVariation
      ((sigmaLaw μ Q).pushforward observe) ≤ error := by
  simpa only [SmallBias.expectation_const] using
    observed_sigma_le_of_bound μ P Q (fun _ => error) bound observe

end
end PerfectCompleteness.ConditionalVariation


namespace PerfectCompleteness.DummyElimination.Slice

noncomputable section

open scoped BigOperators Classical

variable {𝕜 H D K R C : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H] [AddCommGroup D] [Module 𝕜 D]
  [AddCommGroup K] [Module 𝕜 K] [AddCommGroup R] [Module 𝕜 R]
  [AddCommGroup C] [Module 𝕜 C]
  (S : DummyElimination.Slice 𝕜 H D K R C)

abbrev Lifted := {p : (H →ₗ[𝕜] K) × (D →ₗ[𝕜] K) // S.IsLift p.1 p.2}
abbrev ProjectedMatrices := {X : H →ₗ[𝕜] K // S.Projected X}
abbrev HomogeneousMaps := {Z : D →ₗ[𝕜] K // S.Homogeneous Z}

def chosenLift (hne : ∃ X Y, S.IsLift X Y) (X : S.ProjectedMatrices) :
    {Y : D →ₗ[𝕜] K // S.IsLift X.val Y} :=
  ⟨Classical.choose ((S.exists_lift_iff hne X.val).mpr X.property),
    Classical.choose_spec ((S.exists_lift_iff hne X.val).mpr X.property)⟩

def liftedEquivProduct (hne : ∃ X Y, S.IsLift X Y) :
    S.Lifted ≃ S.ProjectedMatrices × S.HomogeneousMaps where
  toFun p :=
    let X : S.ProjectedMatrices := ⟨p.val.1, IsLift.projected S p.property⟩
    (X, S.fiberEquivHomogeneous (S.chosenLift hne X).property ⟨p.val.2, p.property⟩)
  invFun p :=
    let Y := (S.fiberEquivHomogeneous (S.chosenLift hne p.1).property).symm p.2
    ⟨(p.1.val, Y.val), Y.property⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val
        ((S.fiberEquivHomogeneous
          (S.chosenLift hne ⟨p.val.1, IsLift.projected S p.property⟩).property).symm_apply_apply
            ⟨p.val.2, p.property⟩)
  right_inv p := by
    apply Prod.ext
    · rfl
    · exact (S.fiberEquivHomogeneous (S.chosenLift hne p.1).property).apply_symm_apply p.2

@[simp] theorem liftedEquivProduct_fst (hne : ∃ X Y, S.IsLift X Y) (p : S.Lifted) :
    (S.liftedEquivProduct hne p).1.val = p.val.1 := rfl

theorem expect_projected [Fintype (H →ₗ[𝕜] K)] [Fintype (D →ₗ[𝕜] K)]
    (hne : ∃ X Y, S.IsLift X Y) (g : (H →ₗ[𝕜] K) → ℝ) :
    (𝔼 p : S.Lifted, g p.val.1) = (𝔼 X : S.ProjectedMatrices, g X.val) := by
  let : Nonempty S.HomogeneousMaps := ⟨⟨0, by simp [Homogeneous]⟩⟩
  calc
    _ = 𝔼 p : S.ProjectedMatrices × S.HomogeneousMaps, g p.1.val :=
      Fintype.expect_equiv (S.liftedEquivProduct hne) _ _ (fun _ => rfl)
    _ = 𝔼 X : S.ProjectedMatrices, 𝔼 _Z : S.HomogeneousMaps, g X.val := by
      simpa only [Finset.univ_product_univ] using
        (Finset.expect_product (Finset.univ : Finset S.ProjectedMatrices)
          (Finset.univ : Finset S.HomogeneousMaps) (fun p => g p.1.val))
    _ = _ := by simp only [Fintype.expect_const]

end
end PerfectCompleteness.DummyElimination.Slice

end OAI
