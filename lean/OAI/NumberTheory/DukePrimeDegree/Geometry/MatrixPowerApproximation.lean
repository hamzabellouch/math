import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Stable powers of near-identity matrices

The telescoping estimate is the quantitative step needed to recover a
one-parameter subgroup from the velocity of an actual subgroup curve.
The number of factors grows, while their norms are bounded by a fixed
exponential on the reciprocal scale.
-/

noncomputable section
open Filter
open scoped Topology Matrix.Norms.Operator

namespace DukePrimeDegree

private lemma norm_pow_succ_sub_pow_succ_le {A : Type*} [NormedRing A]
    (a b : A) (K : ℝ) (ha : ‖a‖ ≤ K) (hb : ‖b‖ ≤ K) (N : ℕ) :
    ‖a ^ (N + 1) - b ^ (N + 1)‖ ≤ (N + 1 : ℝ) * K ^ N * ‖a - b‖ := by
  have hK : 0 ≤ K := (norm_nonneg a).trans ha
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Nat.cast_succ]
    have he : a ^ (N + 1 + 1) - b ^ (N + 1 + 1) =
        (a ^ (N + 1) - b ^ (N + 1)) * b + a ^ (N + 1) * (a - b) := by
      simp only [pow_succ]
      noncomm_ring
    rw [he]
    have hpow : ‖a ^ (N + 1)‖ ≤ K ^ (N + 1) :=
      (norm_pow_le' a (Nat.succ_pos N)).trans (pow_le_pow_left₀ (norm_nonneg a) ha _)
    calc
      _ ≤ ‖a ^ (N + 1) - b ^ (N + 1)‖ * ‖b‖ + ‖a ^ (N + 1)‖ * ‖a - b‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ ((N + 1 : ℝ) * K ^ N * ‖a - b‖) * K + K ^ (N + 1) * ‖a - b‖ := by
        gcongr
      _ = (N + 1 + 1 : ℝ) * K ^ (N + 1) * ‖a - b‖ := by
        rw [pow_succ]
        ring

/-- The operator norm gives a dimension-free estimate for actual
matrix powers; no entrywise bound is repeatedly amplified. -/
theorem matrix_power_approximation {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (C : ℝ) (hC : 0 ≤ C) (N : ℕ)
    (hA : ‖A‖ ≤ Real.exp (C / (N + 1 : ℝ)))
    (hB : ‖B‖ ≤ Real.exp (C / (N + 1 : ℝ))) :
    ‖A ^ (N + 1) - B ^ (N + 1)‖ ≤ Real.exp C * ((N + 1 : ℝ) * ‖A - B‖) := by
  have hden : (0 : ℝ) < N + 1 := by positivity
  have hdiv : 0 ≤ C / (N + 1 : ℝ) := div_nonneg hC hden.le
  have hmul : (N : ℝ) * (C / (N + 1 : ℝ)) ≤ C := by
    have he : (N + 1 : ℝ) * (C / (N + 1 : ℝ)) = C := by
      field_simp [ne_of_gt hden]
    nlinarith
  have hexp : (Real.exp (C / (N + 1 : ℝ))) ^ N ≤ Real.exp C := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr hmul
  calc
    _ ≤ (N + 1 : ℝ) * (Real.exp (C / (N + 1 : ℝ))) ^ N * ‖A - B‖ :=
      norm_pow_succ_sub_pow_succ_le A B _ hA hB N
    _ ≤ (N + 1 : ℝ) * Real.exp C * ‖A - B‖ := by gcongr
    _ = _ := by ring

/-- If the one-step error is little-o of the reciprocal number of
factors, the products have the same limit. -/
theorem tendsto_matrix_power_difference_zero {n : ℕ}
    (A B : ℕ → Matrix (Fin n) (Fin n) ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ᶠ N in atTop, ‖A N‖ ≤ Real.exp (C / (N + 1 : ℝ)))
    (hB : ∀ᶠ N in atTop, ‖B N‖ ≤ Real.exp (C / (N + 1 : ℝ)))
    (herr : Tendsto (fun N : ℕ => (N + 1 : ℝ) * ‖A N - B N‖) atTop (𝓝 0)) :
    Tendsto (fun N => ‖(A N) ^ (N + 1) - (B N) ^ (N + 1)‖) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
  · filter_upwards [hA, hB] with N hAN hBN
    exact matrix_power_approximation (A N) (B N) C hC N hAN hBN
  · simpa only [mul_zero] using herr.const_mul (Real.exp C)

end DukePrimeDegree

end

end OAI
