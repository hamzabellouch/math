import OAI.NumberTheory.Ostmann.ZeroDensity.DensityKernelStrip
import OAI.NumberTheory.Ostmann.ZeroDensity.GaussianContourShift

namespace OAI

/-! # Shifting the actual finite Dirichlet polynomial to a short positive line -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators

noncomputable def densityFiniteMellin (S : Finset ℕ) (a : ℕ → ℂ) (w : ℂ) : ℂ :=
  ∑ n ∈ S, a n / (n : ℂ) ^ w

 theorem densityFiniteMellin_analytic (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 1 ≤ n) (w : ℂ) : AnalyticAt ℂ (densityFiniteMellin S a) w := by
  apply Finset.analyticAt_fun_sum
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by have := hS n hn; omega : n ≠ 0)
  exact analyticAt_const.div ((differentiable_id.const_cpow (Or.inl hn0)).analyticAt w)
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hn0))

 theorem densityFiniteMellin_norm (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 1 ≤ n) (w : ℂ) (hw : 0 ≤ w.re) :
    ‖densityFiniteMellin S a w‖ ≤ ∑ n ∈ S, ‖a n‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_div, norm_natCast_cpow_of_pos (lt_of_lt_of_le Nat.zero_lt_one (hS n hn))]
  apply div_le_self (norm_nonneg _)
  exact Real.one_le_rpow (by exact_mod_cast hS n hn) hw

noncomputable def densityFiniteKernel (χ : PrimitiveComplexCharacter) (s : ℂ)
    (S : Finset ℕ) (a : ℕ → ℂ) (w : ℂ) : ℂ :=
  densitySquareKernel χ s w * densityFiniteMellin S a w

 theorem densityFiniteKernel_shift (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (S : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, 1 ≤ n)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    (∫ u : ℝ, densityFiniteKernel χ s S a ((c : ℂ) + u * I)) =
      ∫ u : ℝ, densityFiniteKernel χ s S a (1 + u * I) := by
  let K := Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
    2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) *
    ((χ.modulus : ℝ) * (|s.im| + 2)) / c
  apply gaussian_strip_vertical_eq (densityFiniteKernel χ s S a) c 1
    (K * ∑ n ∈ S, ‖a n‖) hc1
  · intro w hw hw1
    exact (densitySquareKernel_analytic χ s w hs (hc.trans_le hw)).mul
      (densityFiniteMellin_analytic S a hS w)
  · intro x hx u
    have hk := densitySquareKernel_strip_bound χ s hs c x u hc hx.1 hx.2
    have hm := densityFiniteMellin_norm S a hS ((x : ℂ) + u * I) (by simp; linarith [hx.1])
    rw [densityFiniteKernel, norm_mul]
    have h := mul_le_mul hk hm (norm_nonneg _) (by positivity)
    convert h using 1
    ring

end Ostmann

end OAI
