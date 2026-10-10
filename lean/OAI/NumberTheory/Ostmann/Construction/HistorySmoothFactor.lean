import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

namespace OAI

/-! # The smooth factors in the expanded arithmetic histories

Compensation-prime powers and spectator transforms are excluded here,
as in the definition of Xi in Section 8 of the manuscript.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def archimedeanLeafFactor (X M s cutoff : ℝ) (ψhat : ℝ → ℂ) : ℂ :=
  (Real.sqrt (X / M) * cutoff : ℝ) * ψhat (-s * X / M)

theorem archimedeanLeafFactor_norm_le (X M s cutoff B A : ℝ) (ψhat : ℝ → ℂ)
    (hcut : |cutoff| ≤ 1) (hψ : ∀ t, ‖ψhat t‖ ≤ B) (_hB : 0 ≤ B)
    (hratio : Real.sqrt (X / M) * B ≤ A) :
    ‖archimedeanLeafFactor X M s cutoff ψhat‖ ≤ A := by
  unfold archimedeanLeafFactor
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (Real.sqrt (X / M) * 1) * B := mul_le_mul
      (mul_le_mul_of_nonneg_left hcut (Real.sqrt_nonneg _)) (hψ _)
      (norm_nonneg _) (by positivity)
    _ ≤ A := by simpa only [mul_one] using hratio

inductive HistorySmoothData : ℕ → Type
  | leaf (modulus frequency cutoff : ℝ) : HistorySmoothData 0
  | node {n : ℕ} (cutoff : ℝ) (left right : HistorySmoothData n) : HistorySmoothData (n + 1)

noncomputable def HistorySmoothData.value (X : ℝ) (ψhat : ℝ → ℂ) :
    {n : ℕ} → HistorySmoothData n → ℂ
  | _, .leaf M s cutoff => archimedeanLeafFactor X M s cutoff ψhat
  | _, .node cutoff left right =>
    (cutoff : ℂ) * left.value X ψhat * star (right.value X ψhat)

def HistorySmoothData.Bounded (X B A : ℝ) : {n : ℕ} → HistorySmoothData n → Prop
  | _, .leaf M _ cutoff => |cutoff| ≤ 1 ∧ Real.sqrt (X / M) * B ≤ A
  | _, .node cutoff left right => |cutoff| ≤ 1 ∧ left.Bounded X B A ∧ right.Bounded X B A

theorem HistorySmoothData.norm_value_le {n : ℕ} (h : HistorySmoothData n)
    (X B A : ℝ) (ψhat : ℝ → ℂ) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hψ : ∀ t, ‖ψhat t‖ ≤ B) (hh : h.Bounded X B A) :
    ‖h.value X ψhat‖ ≤ A ^ (2 ^ n) := by
  induction h with
  | leaf M s cutoff =>
      simpa only [HistorySmoothData.value, pow_zero, pow_one] using
        archimedeanLeafFactor_norm_le X M s cutoff B A ψhat hh.1 hψ hB hh.2
  | @node n cutoff left right ihL ihR =>
      change ‖(cutoff : ℂ) * left.value X ψhat * star (right.value X ψhat)‖ ≤ _
      rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ (1 * A ^ (2 ^ n)) * A ^ (2 ^ n) := mul_le_mul
          (mul_le_mul hh.1 (ihL hh.2.1) (norm_nonneg _) (by norm_num))
          (ihR hh.2.2) (norm_nonneg _) (by positivity)
        _ = A ^ (2 ^ (n + 1)) := by rw [one_mul, ← pow_add, pow_succ]; congr 1; omega

/-- There are two histories, each with exactly 2^n leaves. All node
cutoffs have modulus at most one. -/
theorem smooth_history_pair_norm_le {n : ℕ} (h₁ h₂ : HistorySmoothData n)
    (X B A : ℝ) (ψhat : ℝ → ℂ) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hψ : ∀ t, ‖ψhat t‖ ≤ B) (hh₁ : h₁.Bounded X B A) (hh₂ : h₂.Bounded X B A) :
    ‖h₁.value X ψhat * star (h₂.value X ψhat)‖ ≤ A ^ (2 * 2 ^ n) := by
  rw [norm_mul, norm_star]
  calc
    _ ≤ A ^ (2 ^ n) * A ^ (2 ^ n) := mul_le_mul
      (h₁.norm_value_le X B A ψhat hB hA hψ hh₁)
      (h₂.norm_value_le X B A ψhat hB hA hψ hh₂) (norm_nonneg _) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega

end Ostmann

end OAI
