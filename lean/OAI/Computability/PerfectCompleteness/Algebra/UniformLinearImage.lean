import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import OAI.Computability.PerfectCompleteness.Foundations.FiniteProduct
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI

section

namespace PerfectCompleteness.UniformLinearImage

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

theorem eq_uniform_of_weight_constant {A : Type*} [Fintype A] [Nonempty A]
    (μ : FiniteDistribution A) (constant : ∀ x y, μ.weight x = μ.weight y) :
    μ = FiniteDistribution.uniform A := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change μ.weight x = 1 / (Fintype.card A : ℝ)
  apply (eq_div_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).mpr
  calc
    μ.weight x * (Fintype.card A : ℝ) = ∑ _y : A, μ.weight x := by
      simp [mul_comm]
    _ = ∑ y : A, μ.weight y := by
      apply Finset.sum_congr rfl
      intro y _
      exact constant x y
    _ = 1 := μ.normalized

theorem uniform_pushforward_weight {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [DecidableEq B] (f : A → B) (y : B) :
    ((FiniteDistribution.uniform A).pushforward f).weight y =
      ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card A := by
  classical
  calc
    _ = ∑ x : A, if f x = y then (1 / (Fintype.card A : ℝ)) else 0 := by
      unfold FiniteDistribution.pushforward FiniteDistribution.uniform
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : f x = y <;> simp [h]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp [nsmul_eq_mul, div_eq_mul_inv]

theorem uniform_pushforward_addHom {A B : Type*}
    [AddGroup A] [AddMonoid B] [Fintype A] [Fintype B]
    (f : A →+ B) (surjective : Function.Surjective f) :
    (FiniteDistribution.uniform A).pushforward f = FiniteDistribution.uniform B := by
  classical
  apply eq_uniform_of_weight_constant
  intro y z
  rw [uniform_pushforward_weight, uniform_pushforward_weight,
    AddMonoidHom.card_fiber_eq_of_mem_range f (surjective y) (surjective z)]

theorem uniform_pushforward_linearMap {R A B : Type*} [Semiring R]
    [AddCommGroup A] [AddCommMonoid B] [Module R A] [Module R B]
    [Fintype A] [Fintype B] (f : A →ₗ[R] B) (surjective : Function.Surjective f) :
    (FiniteDistribution.uniform A).pushforward f = FiniteDistribution.uniform B :=
  uniform_pushforward_addHom f.toAddMonoidHom surjective

section Product

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem law_uniform [∀ i, Nonempty (Ω i)] :
    FiniteProduct.law (fun i => FiniteDistribution.uniform (Ω i)) =
      FiniteDistribution.uniform ((i : I) → Ω i) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∏ i, 1 / (Fintype.card (Ω i) : ℝ)) =
    1 / (Fintype.card ((i : I) → Ω i) : ℝ)
  simp only [Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib,
    Finset.prod_const_one]

variable {R V : Type*} [Semiring R] [AddCommGroup V] [Module R V]
  [∀ i, AddCommGroup (Ω i)] [∀ i, Module R (Ω i)]

def linearSum (maps : (i : I) → Ω i →ₗ[R] V) : ((i : I) → Ω i) →ₗ[R] V where
  toFun x := ∑ i, maps i (x i)
  map_add' x y := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c x := by simp only [Pi.smul_apply, map_smul, Finset.smul_sum,
    RingHom.id_apply]

omit [DecidableEq I] [∀ index, Fintype (Ω index)] in
@[simp] theorem linearSum_apply (maps : (i : I) → Ω i →ₗ[R] V)
    (x : (i : I) → Ω i) : linearSum maps x = ∑ i, maps i (x i) := rfl

variable [Fintype V]

theorem product_uniform_linear_image (f : ((i : I) → Ω i) →ₗ[R] V)
    (surjective : Function.Surjective f) :
    (FiniteProduct.law (fun i => FiniteDistribution.uniform (Ω i))).pushforward f =
      FiniteDistribution.uniform V := by
  rw [law_uniform]
  exact uniform_pushforward_linearMap f surjective

theorem product_uniform_sum_image (maps : (i : I) → Ω i →ₗ[R] V)
    (surjective : Function.Surjective (linearSum maps)) :
    (FiniteProduct.law (fun i => FiniteDistribution.uniform (Ω i))).pushforward
        (fun x => ∑ i, maps i (x i)) = FiniteDistribution.uniform V :=
  product_uniform_linear_image (linearSum maps) surjective

end Product
end
end PerfectCompleteness.UniformLinearImage

end

end OAI
