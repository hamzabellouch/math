import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped BigOperators

namespace TwoPointCorrelations

/-- The standard Liouville function, viewed as complex valued. Its value at zero
is zero, as in mathlib; only positive arguments occur in the main statements. -/
noncomputable def liouville (n : ℕ) : ℂ := ArithmeticFunction.liouville n

/-- An ordinary sum, with weight one on each positive integer at most `N`. -/
def correlationSum (f g : ℕ → ℂ) (h₁ h₂ N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, f (n + h₁) * g (n + h₂)

/-- The ordinary affine correlation, allowing nonunit coefficients. -/
def affineSum (f g : ℕ → ℂ) (a₁ a₂ b₁ b₂ N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, f (a₁ * n + b₁) * g (a₂ * n + b₂)

/-- The progression sum includes every residue class, including zero. -/
def progressionSum (f g : ℕ → ℂ) (h l b N : ℕ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n % l = b % l), f n * g (n + h)

/-- Ordinary multiplicativity is required only for coprime positive arguments;
this also permits the identically zero function, as does the manuscript. -/
def Multiplicative (f : ℕ → ℂ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → f (m * n) = f m * f n

def OneBounded (f : ℕ → ℂ) : Prop := ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1

@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h

/-- Multiplying the two affine arguments by the opposite slopes gives an exact
identity. There is no coprimality restriction on any coefficient. -/
theorem liouville_affine_dilation (a₁ a₂ b₁ b₂ n : ℕ)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    liouville (a₁ * n + b₁) * liouville (a₂ * n + b₂) =
      liouville (a₁ * a₂) * liouville (a₂ * (a₁ * n + b₁)) *
        liouville (a₁ * (a₂ * n + b₂)) := by
  have hs := liouville_sq (Nat.mul_ne_zero ha₁ ha₂)
  calc
    _ = liouville (a₁ * a₂) ^ 2 *
        (liouville (a₁ * n + b₁) * liouville (a₂ * n + b₂)) := by rw [hs, one_mul]
    _ = _ := by simp only [liouville_mul]; ring

/-- The orientation with `a₂ b₁ ≤ a₁ b₂`; the opposite orientation is obtained
by swapping the two factors. This is manuscript equation (q:quant-affine-identity). -/
theorem liouville_affine_ordered (a₁ a₂ b₁ b₂ n : ℕ)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (horder : a₂ * b₁ ≤ a₁ * b₂) :
    liouville (a₁ * n + b₁) * liouville (a₂ * n + b₂) =
      liouville (a₁ * a₂) * liouville (a₁ * a₂ * n + a₂ * b₁) *
        liouville (a₁ * a₂ * n + a₂ * b₁ + (a₁ * b₂ - a₂ * b₁)) := by
  rw [liouville_affine_dilation a₁ a₂ b₁ b₂ n ha₁ ha₂]
  congr 2
  · congr 1; ring
  · calc
      a₁ * (a₂ * n + b₂) = a₁ * a₂ * n + a₁ * b₂ := by ring
      _ = a₁ * a₂ * n + a₂ * b₁ + (a₁ * b₂ - a₂ * b₁) := by omega

theorem liouville_multiplicative : Multiplicative liouville := by
  intro m n _ _ _
  exact liouville_mul m n

theorem liouville_oneBounded : OneBounded liouville := by
  intro n hn
  have hs : ‖liouville n‖ ^ 2 = 1 := by
    rw [← norm_pow, liouville_sq hn.ne', norm_one]
  nlinarith [norm_nonneg (liouville n)]

end TwoPointCorrelations

end OAI
