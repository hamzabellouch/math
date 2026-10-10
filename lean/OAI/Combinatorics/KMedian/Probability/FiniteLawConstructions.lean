import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteLaws

namespace OAI

namespace MetricKMedian.FiniteLaw

noncomputable def dirac {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (ω₀ : Ω) : FiniteLaw Ω where
  weight ω := if ω=ω₀ then 1 else 0
  nonneg ω := by split_ifs <;> norm_num
  total := by simp

theorem expect_dirac {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (ω₀ : Ω) (f : Ω → ℝ) :
    (dirac ω₀).expect f = f ω₀ := by simp [expect, dirac]

noncomputable def mix {Ω : Type*} [Fintype Ω] (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (μ ν : FiniteLaw Ω) : FiniteLaw Ω where
  weight ω := θ*μ.weight ω+(1-θ)*ν.weight ω
  nonneg ω := add_nonneg (mul_nonneg hθ0 (μ.nonneg ω))
    (mul_nonneg (sub_nonneg.mpr hθ1) (ν.nonneg ω))
  total := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    μ.total, ν.total]; ring

theorem expect_mix {Ω : Type*} [Fintype Ω] (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (μ ν : FiniteLaw Ω) (f : Ω → ℝ) :
    (mix θ hθ0 hθ1 μ ν).expect f = θ*μ.expect f+(1-θ)*ν.expect f := by
  simp only [expect, mix, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

noncomputable def product {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (μ : I → FiniteLaw Ω) : FiniteLaw (I → Ω) where
  weight ω := ∏ i, (μ i).weight (ω i)
  nonneg ω := Finset.prod_nonneg (fun i _ => (μ i).nonneg (ω i))
  total := by rw [← Fintype.prod_sum]; simp only [FiniteLaw.total, Finset.prod_const_one]

theorem expect_product {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (μ : I → FiniteLaw Ω) (f : I → Ω → ℝ) :
    (product μ).expect (fun ω => ∏ i, f i (ω i)) = ∏ i, (μ i).expect (f i) := by
  simp only [expect, product, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i ω => (μ i).weight ω*f i ω)).symm

theorem product_marginal {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (μ : I → FiniteLaw Ω) (i : I) (f : Ω → ℝ) :
    (product μ).expect (fun ω => f (ω i)) = (μ i).expect f := by
  have hpoint : ∀ ω : I → Ω, f (ω i) = ∏ j, if j=i then f (ω j) else 1 := by
    intro ω
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [hpoint]
  rw [expect_product μ (fun j x => if j=i then f x else 1)]
  have hfactor : ∀ j, (μ j).expect (fun x => if j=i then f x else 1) =
      if j=i then (μ i).expect f else 1 := by
    intro j
    by_cases hji : j=i
    · subst j; simp only [ite_true]
    · simp only [ite_eq_right hji, expect_const]
  simp_rw [hfactor]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]

theorem product_pair {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (μ : I → FiniteLaw Ω) {i j : I} (hij : i ≠ j) (f h : Ω → ℝ) :
    (product μ).expect (fun ω => f (ω i)*h (ω j)) = (μ i).expect f*(μ j).expect h := by
  let F : I → Ω → ℝ := fun k x => if k=i then f x else if k=j then h x else 1
  have hprod : ∀ (a b : ℝ),
      (∏ k, if k=i then a else if k=j then b else 1) = a*b := by
    intro a b
    have hpoint : ∀ k, (if k=i then a else if k=j then b else 1) =
        (if k=i then a else 1)*(if k=j then b else 1) := by
      intro k
      by_cases hki : k=i
      · subst k; simp [hij]
      · simp [hki]
    simp_rw [hpoint, Finset.prod_mul_distrib]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  have hpoint : ∀ ω : I → Ω, f (ω i)*h (ω j) = ∏ k, F k (ω k) := by
    intro ω
    have hk : ∀ k, F k (ω k) = if k=i then f (ω i) else if k=j then h (ω j) else 1 := by
      intro k
      dsimp only [F]
      split_ifs with hki hkj
      · subst k; rfl
      · subst k; rfl
      · rfl
    simp_rw [hk]
    exact (hprod _ _).symm
  simp_rw [hpoint]
  rw [expect_product]
  have hfactor : ∀ k, (μ k).expect (F k) =
      if k=i then (μ i).expect f else if k=j then (μ j).expect h else 1 := by
    intro k
    by_cases hki : k=i
    · subst k; simp only [F, ite_true]
    · by_cases hkj : k=j
      · subst k; simp only [F, ite_eq_right hki, ite_true]
      · simp only [F, ite_eq_right hki, ite_eq_right hkj, expect_const]
  simp_rw [hfactor]
  exact hprod _ _

end MetricKMedian.FiniteLaw

end OAI
