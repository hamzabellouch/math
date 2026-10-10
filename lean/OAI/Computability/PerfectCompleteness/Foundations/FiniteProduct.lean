import Mathlib.Data.Fintype.BigOperators
import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaceEquivLemmas
import OAI.Computability.UniqueGames.Foundations.ValueLemmas

namespace OAI

section

namespace PerfectCompleteness.FiniteProduct

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def law (P : (i : I) → FiniteDistribution (Ω i)) :
    FiniteDistribution ((i : I) → Ω i) where
  weight x := ∏ i, (P i).weight (x i)
  nonnegative x := Finset.prod_nonneg fun i _ => (P i).nonnegative (x i)
  normalized := by
    rw [← Fintype.prod_sum]
    simp only [FiniteDistribution.normalized, Finset.prod_const_one]

theorem expectation_product (P : (i : I) → FiniteDistribution (Ω i))
    (f : (i : I) → Ω i → ℝ) :
    (law P).expectation (fun x => ∏ i, f i (x i)) =
      ∏ i, (P i).expectation (f i) := by
  change (∑ x : (i : I) → Ω i, (∏ i, (P i).weight (x i)) *
      (∏ i, f i (x i))) = ∏ i, ∑ a, (P i).weight a * f i a
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (P i).weight a * f i a)).symm

def factor (i : I) (f : Ω i → ℝ) (j : I) (a : Ω j) : ℝ :=
  if h : j = i then f (h ▸ a) else 1

omit [Fintype I] [∀ index, Fintype (Ω index)] in
@[simp] theorem factor_self (i : I) (f : Ω i → ℝ) (a : Ω i) :
    factor i f i a = f a := by simp [factor]

omit [Fintype I] [∀ index, Fintype (Ω index)] in
@[simp] theorem factor_other (i j : I) (h : j ≠ i) (f : Ω i → ℝ) (a : Ω j) :
    factor i f j a = 1 := by simp [factor, h]

omit [Fintype I] [∀ index, Fintype (Ω index)] in
@[simp] theorem factor_function_self (i : I) (f : Ω i → ℝ) :
    factor i f i = f := by funext a; exact factor_self i f a

omit [Fintype I] [∀ index, Fintype (Ω index)] in
@[simp] theorem factor_function_other (i j : I) (h : j ≠ i) (f : Ω i → ℝ) :
    factor i f j = fun _ => 1 := by funext a; exact factor_other i j h f a

omit [∀ index, Fintype (Ω index)] in
theorem product_factor (i : I) (f : Ω i → ℝ) (x : (j : I) → Ω j) :
    (∏ j, factor i f j (x j)) = f (x i) := by
  classical
  rw [Finset.prod_eq_single i]
  · exact factor_self i f (x i)
  · intro j _ h
    exact factor_other i j h f (x j)
  · simp

theorem expectation_factor_product (P : (i : I) → FiniteDistribution (Ω i))
    (i : I) (f : Ω i → ℝ) :
    (∏ j, (P j).expectation (factor i f j)) = (P i).expectation f := by
  classical
  rw [Finset.prod_eq_single i]
  · congr 1
    funext a
    exact factor_self i f a
  · intro j _ h
    rw [factor_function_other i j h, SmallBias.expectation_const]
  · simp

theorem expectation_eval (P : (i : I) → FiniteDistribution (Ω i))
    (i : I) (f : Ω i → ℝ) :
    (law P).expectation (fun x => f (x i)) = (P i).expectation f := by
  calc
    _ = (law P).expectation (fun x => ∏ j, factor i f j (x j)) := by
      apply FiniteDistribution.expectation_congr
      intro x
      exact (product_factor i f x).symm
    _ = ∏ j, (P j).expectation (factor i f j) := expectation_product P _
    _ = _ := expectation_factor_product P i f

theorem expectation_eval_mul (P : (i : I) → FiniteDistribution (Ω i))
    (i j : I) (hij : i ≠ j) (f : Ω i → ℝ) (g : Ω j → ℝ) :
    (law P).expectation (fun x => f (x i) * g (x j)) =
      (P i).expectation f * (P j).expectation g := by
  have hfactor : ∀ k,
      (P k).expectation (fun a => factor i f k a * factor j g k a) =
      (P k).expectation (factor i f k) * (P k).expectation (factor j g k) := by
    intro k
    by_cases hki : k = i
    · subst k
      simp only [factor_other j i hij, factor_function_other j i hij,
        SmallBias.expectation_const, mul_one]
    · simp only [factor_other i k hki, factor_function_other i k hki,
        SmallBias.expectation_const, one_mul]
  calc
    _ = (law P).expectation
        (fun x => ∏ k, factor i f k (x k) * factor j g k (x k)) := by
      apply FiniteDistribution.expectation_congr
      intro x
      rw [Finset.prod_mul_distrib, product_factor i f x, product_factor j g x]
    _ = ∏ k, (P k).expectation (fun a => factor i f k a * factor j g k a) :=
      expectation_product P (fun k a => factor i f k a * factor j g k a)
    _ = (∏ k, (P k).expectation (factor i f k)) *
        (∏ k, (P k).expectation (factor j g k)) := by
      simp only [hfactor, Finset.prod_mul_distrib]
    _ = _ := by rw [expectation_factor_product P i f, expectation_factor_product P j g]

end
end PerfectCompleteness.FiniteProduct

end

end OAI
