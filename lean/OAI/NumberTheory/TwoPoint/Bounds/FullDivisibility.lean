import OAI.NumberTheory.TwoPoint.Bounds.LiouvilleDivisorExtraction
import OAI.NumberTheory.TwoPoint.Bounds.NearbyCutoffs
import Mathlib.Algebra.Order.Floor.Semifield

namespace OAI

/-! The full-divisibility term extracts the original progression
correlation at a cutoff in the same logarithmic bin. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def fullLiouvilleProfile (l : ℕ) [NeZero l] (b : ZMod l)
    (u h n : ℕ) : ℂ :=
  natDivisibilityIndicator u n *
    (progressionSequence liouville l (b * (u : ZMod l)) n * liouville (n + h * u))

lemma fullLiouvilleProfile_prefix (l : ℕ) [NeZero l] (b : ZMod l)
    (u h N : ℕ) (hu : 0 < u) (hunit : IsUnit (u : ZMod l)) :
    positivePrefix (fullLiouvilleProfile l b u h) N =
      positivePrefix (fun n => progressionSequence liouville l b n * liouville (n + h)) (N / u) := by
  unfold fullLiouvilleProfile
  rw [divisibility_positivePrefix _ u N hu]
  congr 1
  funext v
  simpa only [Nat.cast_one, mul_one] using liouville_progression_dilate l b u v 1 h hu hunit

lemma progressionLiouvilleProfile_oneBounded (l : ℕ) [NeZero l] (b : ZMod l) (h : ℕ) :
    OneBounded (fun n => progressionSequence liouville l b n * liouville (n + h)) := by
  intro n hn
  dsimp only [progressionSequence]
  split_ifs
  · rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul (liouville_oneBounded n hn)
        (liouville_oneBounded (n + h) (by omega)) (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  · simp only [zero_mul, norm_zero, zero_le_one]

lemma fullLiouvilleProfile_real_prefix (l : ℕ) [NeZero l] (b : ZMod l)
    (u h : ℕ) (hu : 0 < u) (hunit : IsUnit (u : ZMod l)) (T : ℝ) (hT : 0 < T) :
    positivePrefix (fullLiouvilleProfile l b u h) ⌊T⌋₊ / (T : ℂ) =
      (1 / (u : ℂ)) *
        (positivePrefix (fun n => progressionSequence liouville l b n * liouville (n + h))
          ⌊T / u⌋₊ / ((T / u : ℝ) : ℂ)) := by
  rw [fullLiouvilleProfile_prefix l b u h _ hu hunit, Nat.floor_div_natCast]
  push_cast
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  field_simp

lemma fullLiouvilleProfile_bin_error (l : ℕ) [NeZero l] (b : ZMod l)
    (u h : ℕ) (hu : 0 < u) (hunit : IsUnit (u : ZMod l))
    (X T η : ℝ) (hX : 0 < X) (hη : 0 ≤ η)
    (hlo : X * Real.exp (-η) ≤ T / u) (hhi : T / u ≤ X) :
    ‖positivePrefix (fullLiouvilleProfile l b u h) ⌊T⌋₊ / (T : ℂ) -
      (1 / (u : ℂ)) *
        (positivePrefix (fun n => progressionSequence liouville l b n * liouville (n + h))
          ⌊X⌋₊ / (X : ℂ))‖ ≤ (1 / (u : ℝ)) * (2 * η + 1 / X) := by
  have hY : 0 < T / u := (mul_pos hX (Real.exp_pos _)).trans_le hlo
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hT : 0 < T := by
    rcases div_pos_iff.mp hY with hp | hn
    · exact hp.1
    · linarith [hn.2]
  rw [fullLiouvilleProfile_real_prefix l b u h hu hunit T hT, ← mul_sub, norm_mul]
  have hc := real_prefix_log_bin _ (progressionLiouvilleProfile_oneBounded l b h)
    X (T / u) η hX hη hlo hhi
  simpa only [norm_div, norm_one, Complex.norm_natCast] using
    mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 1 / (u : ℝ))

lemma full_divisibility_bin_sum_error (l : ℕ) [NeZero l] (b : ZMod l)
    (h : ℕ) (U : Finset ℕ) (weight : ℕ → ℝ)
    (hweight : ∀ u ∈ U, 0 ≤ weight u) (hu : ∀ u ∈ U, 0 < u)
    (hunit : ∀ u ∈ U, IsUnit (u : ZMod l)) (X T η : ℝ)
    (hX : 0 < X) (hη : 0 ≤ η)
    (hlo : ∀ u ∈ U, X * Real.exp (-η) ≤ T / u)
    (hhi : ∀ u ∈ U, T / u ≤ X) :
    ‖(∑ u ∈ U, (weight u : ℂ) *
        (positivePrefix (fullLiouvilleProfile l b u h) ⌊T⌋₊ / (T : ℂ))) -
      ((∑ u ∈ U, weight u / (u : ℝ) : ℝ) : ℂ) *
        (positivePrefix (fun n => progressionSequence liouville l b n * liouville (n + h))
          ⌊X⌋₊ / (X : ℂ))‖ ≤
      (∑ u ∈ U, weight u / (u : ℝ)) * (2 * η + 1 / X) := by
  let F := positivePrefix
    (fun n => progressionSequence liouville l b n * liouville (n + h)) ⌊X⌋₊ / (X : ℂ)
  have he : (∑ u ∈ U, (weight u : ℂ) *
      (positivePrefix (fullLiouvilleProfile l b u h) ⌊T⌋₊ / (T : ℂ))) -
      ((∑ u ∈ U, weight u / (u : ℝ) : ℝ) : ℂ) * F =
      ∑ u ∈ U, (weight u : ℂ) *
        ((positivePrefix (fullLiouvilleProfile l b u h) ⌊T⌋₊ / (T : ℂ)) -
          (1 / (u : ℂ)) * F) := by
    push_cast
    rw [sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro u _
    ring
  change ‖_ - _ * F‖ ≤ _
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ u ∈ U, weight u * ((1 / (u : ℝ)) * (2 * η + 1 / X)) := by
      apply sum_le_sum
      intro u huU
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hweight u huU)]
      exact mul_le_mul_of_nonneg_left
        (fullLiouvilleProfile_bin_error l b u h (hu u huU) (hunit u huU) X T η hX hη
          (hlo u huU) (hhi u huU)) (hweight u huU)
    _ = _ := by
      rw [sum_mul]
      apply sum_congr rfl
      intro u _
      ring

end TwoPointCorrelations

end OAI
