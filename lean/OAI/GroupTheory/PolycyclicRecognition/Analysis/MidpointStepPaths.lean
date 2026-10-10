import OAI.GroupTheory.PolycyclicRecognition.Algebra.MidpointGrids
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

/-! # Step paths through successively refined midpoint grids -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {X : Type*} [MetricSpace X]

def midpointStepPath (h : HasMetricMidpoints X) (x y : X) (n : ℕ)
    (t : Icc (0 : ℝ) 1) : X :=
  midpointGrid h x y n ⌊(2 : ℝ) ^ n * (t : ℝ)⌋₊

theorem midpointStepPath_zero (h : HasMetricMidpoints X) (x y : X) (n : ℕ) :
    midpointStepPath h x y n ⟨0, by simp⟩ = x := by
  simp [midpointStepPath, midpointGrid_zero]

theorem midpointStepPath_one (h : HasMetricMidpoints X) (x y : X) (n : ℕ) :
    midpointStepPath h x y n ⟨1, by simp⟩ = y := by
  have heq : ⌊(2 : ℝ) ^ n⌋₊ = 2 ^ n := by
    rw [← Nat.cast_ofNat, ← Nat.cast_pow, Nat.floor_natCast]
  simp only [midpointStepPath, mul_one, heq, midpointGrid_last]

theorem midpointStepPath_ball (h : HasMetricMidpoints X) (x y : X)
    (n : ℕ) (t : Icc (0 : ℝ) 1) :
    dist (midpointStepPath h x y n t) x ≤ dist x y := by
  have hk : ⌊(2 : ℝ) ^ n * (t : ℝ)⌋₊ ≤ 2 ^ n := by
    apply Nat.floor_le_of_le
    push_cast
    exact mul_le_of_le_one_right (by positivity) t.property.2
  have hb := midpointGrid_dist h x y n (Nat.zero_le _) hk
  rw [midpointGrid_zero, Nat.sub_zero] at hb
  rw [dist_comm]
  apply hb.trans
  have hk' : (⌊(2 : ℝ) ^ n * (t : ℝ)⌋₊ : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hk
  calc
    _ ≤ (2 : ℝ) ^ n * (dist x y / (2 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_right hk' (by positivity)
    _ = dist x y := by field_simp

theorem midpointStepPath_dist_of_le (h : HasMetricMidpoints X) (x y : X)
    (n : ℕ) (s t : Icc (0 : ℝ) 1) (hst : (s : ℝ) ≤ t) :
    dist (midpointStepPath h x y n s) (midpointStepPath h x y n t) ≤
      dist x y * ((t : ℝ) - s) + dist x y / (2 : ℝ) ^ n := by
  let k := ⌊(2 : ℝ) ^ n * (s : ℝ)⌋₊
  let l := ⌊(2 : ℝ) ^ n * (t : ℝ)⌋₊
  have hkl : k ≤ l := Nat.floor_mono (mul_le_mul_of_nonneg_left hst (by positivity))
  have hl : l ≤ 2 ^ n := by
    apply Nat.floor_le_of_le
    push_cast
    exact mul_le_of_le_one_right (by positivity) t.property.2
  have hb := midpointGrid_dist h x y n hkl hl
  change dist (midpointStepPath h x y n s) (midpointStepPath h x y n t) ≤ _ at hb
  apply hb.trans
  rw [Nat.cast_sub hkl]
  have hs := Nat.lt_floor_add_one ((2 : ℝ) ^ n * (s : ℝ))
  have ht := Nat.floor_le (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ n) t.property.1)
  change (2 : ℝ) ^ n * (s : ℝ) < (k : ℝ) + 1 at hs
  change (l : ℝ) ≤ (2 : ℝ) ^ n * (t : ℝ) at ht
  have hdiff : (l : ℝ) - k ≤ (2 : ℝ) ^ n * ((t : ℝ) - s) + 1 := by nlinarith
  calc
    _ ≤ ((2 : ℝ) ^ n * ((t : ℝ) - s) + 1) * (dist x y / (2 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_right hdiff (by positivity)
    _ = _ := by field_simp

theorem midpointStepPath_dist (h : HasMetricMidpoints X) (x y : X)
    (n : ℕ) (s t : Icc (0 : ℝ) 1) :
    dist (midpointStepPath h x y n s) (midpointStepPath h x y n t) ≤
      dist x y * |(s : ℝ) - t| + dist x y / (2 : ℝ) ^ n := by
  rcases le_total (s : ℝ) t with hst | hts
  · rw [abs_of_nonpos (sub_nonpos.mpr hst)]
    convert midpointStepPath_dist_of_le h x y n s t hst using 1
    ring
  · rw [dist_comm, abs_of_nonneg (sub_nonneg.mpr hts)]
    exact midpointStepPath_dist_of_le h x y n t s hts

end PolycyclicRecognition

end

end OAI
