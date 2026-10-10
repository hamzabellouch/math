import Mathlib

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution
open Matrix
open scoped RealInnerProductSpace
open scoped BigOperators

namespace HarmonicCounterexample.FrequencyArithmetic

def bandNumerator (k : ℕ) : ℝ :=
  ∑ l ∈ Finset.Ico (k / 2 + 1) (k + 2), (2 * (l : ℝ) + 1) * ((l : ℝ) + 1)

def bandMean (k : ℕ) : ℝ :=
  bandNumerator k / (((k : ℝ) + 2)^2 - (((k / 2 : ℕ) : ℝ) + 1)^2)

lemma weighted_round_sum (n : ℕ) :
    (∑ l ∈ Finset.range n, (2 * (l : ℝ) + 1) * ((l : ℝ) + 1)) =
      (n : ℝ) * ((n : ℝ) + 1) * (4 * (n : ℝ) - 1) / 6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma bandNumerator_eq (k : ℕ) :
    bandNumerator k =
      ((k : ℝ) + 2) * ((k : ℝ) + 3) * (4 * ((k : ℝ) + 2) - 1) / 6 -
      (((k / 2 : ℕ) : ℝ) + 1) * (((k / 2 : ℕ) : ℝ) + 2) *
        (4 * (((k / 2 : ℕ) : ℝ) + 1) - 1) / 6 := by
  unfold bandNumerator
  rw [Finset.sum_Ico_eq_sub _ (by omega), weighted_round_sum, weighted_round_sum]
  push_cast
  ring

lemma quotient_bound {b K : ℝ} (hK : 0 < K) (hb : 0 ≤ b) (hhalf : 2 * b ≤ K) :
    (K * (K + 1) * (4 * K - 1) / 6 - b * (b + 1) * (4 * b - 1) / 6) /
      (K^2 - b^2) ≤ (7/9 : ℝ) * K + 1/2 := by
  have hlt : b < K := by linarith
  have hden : 0 < K^2 - b^2 := by nlinarith
  apply (div_le_iff₀ hden).2
  apply sub_nonneg.mp
  have hid : ((7/9 : ℝ) * K + 1/2) * (K^2 - b^2) -
        (K * (K + 1) * (4 * K - 1) / 6 - b * (b + 1) * (4 * b - 1) / 6) =
      (K - b) * ((K - 2 * b) * (K + 3 * b) / 9 + 1/6) := by ring
  rw [hid]
  exact mul_nonneg (sub_nonneg.mpr hlt.le)
    (add_nonneg (div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num))
      (by norm_num))

lemma bandMean_bound (k : ℕ) :
    bandMean k ≤ (7/9 : ℝ) * ((k : ℝ) + 2) + 1/2 := by
  have hh : 2 * ((k / 2 : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (show 2 * (k / 2) ≤ k by omega)
  unfold bandMean
  rw [bandNumerator_eq]
  convert quotient_bound (b := ((k / 2 : ℕ) : ℝ) + 1) (K := (k : ℝ) + 2)
    (by positivity) (by positivity) (by linarith) using 1
  ring

theorem arithmetic_frequency_margin (k : ℕ) (hk : 14 ≤ k) :
    (107/100 : ℝ) * (((k / 2 : ℕ) : ℝ) + 1) < (k : ℝ) ∧
      (107/100 : ℝ) * bandMean k < (k : ℝ) := by
  have hk' : (14 : ℝ) ≤ k := by exact_mod_cast hk
  have hh : 2 * ((k / 2 : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (show 2 * (k / 2) ≤ k by omega)
  constructor
  · linarith
  · calc
      (107/100 : ℝ) * bandMean k ≤
          (107/100 : ℝ) * ((7/9 : ℝ) * ((k : ℝ) + 2) + 1/2) :=
        mul_le_mul_of_nonneg_left (bandMean_bound k) (by norm_num)
      _ < (k : ℝ) := by linarith

end HarmonicCounterexample.FrequencyArithmetic

end

end OAI
