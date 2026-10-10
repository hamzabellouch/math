import OAI.Analysis.IrrationalRotation.Model.LaurentConvolution
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233

structure ProductScaleData where
  m : ℕ → ℕ
  K : ℕ → ℕ
  G : ℕ → ℕ
  L : ℕ → ℝ
  C : ℕ → ℝ
  ε : ℕ → ℝ

namespace ProductScaleData

def prefixCount (p : ProductScaleData) (n : ℕ) : ℕ :=
  ∑ r ∈ Finset.range n, p.m r

def prefixCost (p : ProductScaleData) (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.range n, p.C r * p.m r

def coefficientBound (p : ProductScaleData) (n : ℕ) : ℝ :=
  Real.exp (((p.K n : ℝ) + 1) * p.prefixCost n)

def kappa (n : ℕ) : ℝ := 1 / (100 * ((n + 1 : ℕ) : ℝ))

def N (p : ProductScaleData) (n : ℕ) : ℝ := (p.m n : ℝ) * p.K n

def a (p : ProductScaleData) (n : ℕ) : ℝ := (p.G n : ℝ) / p.m n

def b (p : ProductScaleData) (n : ℕ) : ℝ := (p.m n : ℝ) ^ (-(19 / 20 : ℝ))

end ProductScaleData

open Invariant233.FiniteWindow

structure ProductScaleLaws (p : ProductScaleData) : Prop where
  initial_K : p.K 0 = 100
  initial_G : p.G 0 = 1
  K_pos : ∀ n, 0 < p.K n
  G_pos : ∀ n, 0 < p.G n
  epsilon_pos : ∀ n, 0 < p.ε n
  L_ge_one : ∀ n, 1 ≤ p.L n
  L_monotone : Monotone p.L
  C_eq : ∀ n, p.C n = max (p.L n) ((p.K n : ℝ) ^ 2)
  polynomial_lower : ∀ n, ∀ A B : ℤ → ℂ,
    (∀ i, |i| ≤ (p.K n : ℤ) → ‖A i‖ ≤ p.coefficientBound n) →
    (∀ i, |i| ≤ (p.K n : ℤ) → ‖B i‖ ≤ p.coefficientBound n) →
    1 / ((n + 1 : ℕ) : ℝ) ≤ ‖A 0‖ →
    1 / ((n + 1 : ℕ) : ℝ) ≤ ‖B 0‖ →
    ∃ i : ℕ, i ≤ 2 * p.K n ∧ p.ε n ≤ ‖convolution (p.K n) A B i‖
  polynomial_attenuation : ∀ n,
    ((2 * p.K n + 1 : ℕ) : ℝ) * 3 * Real.exp (-p.L n / 10000) ≤
      p.ε n / ((n + 1 : ℕ) : ℝ)
  gain_attenuation : ∀ n,
    p.L n ≤ ProductScaleData.kappa (n + 1) * Real.sqrt (p.G (n + 1) : ℝ)
  m_ge_K : ∀ n, p.K n ≤ p.m n
  m_ge_pow : ∀ n, 2 ^ (n + 1) ≤ p.m n
  m_ge_G : ∀ n, 4 * p.G n ≤ p.m n
  m_ge_100 : ∀ n, 100 ≤ p.m n
  prefix_count_le : ∀ n, (p.prefixCount n : ℝ) ≤ (p.m n : ℝ) / 100
  m_attenuation : ∀ n,
    p.L n ≤ ProductScaleData.kappa n * (p.m n : ℝ) ^ (1 / 40 : ℝ)
  next_K : ∀ n,
    p.K (n + 1) = ⌈(p.m n : ℝ) ^ ((3 / 4 : ℝ) * p.m n)⌉₊
  next_gap : ∀ n, (p.G (n + 1) : ℝ) * p.K (n + 1) <
    (p.m n : ℝ) ^ ((4 / 5 : ℝ) * p.m n)
  K_double : ∀ n, 2 * p.K n < p.K (n + 1)

end Invariant233

end

end OAI
