import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProperMetricMidpoints

namespace OAI

/-! # Finite dyadic grids obtained by inserting metric midpoints -/

noncomputable section
namespace PolycyclicRecognition

variable {X : Type*} [MetricSpace X]

def HasMetricMidpoints (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ z : X, dist x z ≤ dist x y / 2 ∧ dist z y ≤ dist x y / 2

def metricMidpoint (h : HasMetricMidpoints X) (x y : X) : X :=
  Classical.choose (h x y)

theorem metricMidpoint_left (h : HasMetricMidpoints X) (x y : X) :
    dist x (metricMidpoint h x y) ≤ dist x y / 2 :=
  (Classical.choose_spec (h x y)).1

theorem metricMidpoint_right (h : HasMetricMidpoints X) (x y : X) :
    dist (metricMidpoint h x y) y ≤ dist x y / 2 :=
  (Classical.choose_spec (h x y)).2

def midpointGrid (h : HasMetricMidpoints X) (x y : X) : ℕ → ℕ → X
  | 0, k => if k = 0 then x else y
  | n + 1, k => if k % 2 = 0 then midpointGrid h x y n (k / 2)
      else metricMidpoint h (midpointGrid h x y n (k / 2))
        (midpointGrid h x y n (k / 2 + 1))

theorem midpointGrid_even (h : HasMetricMidpoints X) (x y : X) (n k : ℕ) :
    midpointGrid h x y (n + 1) (2 * k) = midpointGrid h x y n k := by
  simp [midpointGrid]

theorem midpointGrid_odd (h : HasMetricMidpoints X) (x y : X) (n k : ℕ) :
    midpointGrid h x y (n + 1) (2 * k + 1) =
      metricMidpoint h (midpointGrid h x y n k) (midpointGrid h x y n (k + 1)) := by
  simp [midpointGrid, Nat.add_div, Nat.add_mod]

theorem midpointGrid_zero (h : HasMetricMidpoints X) (x y : X) (n : ℕ) :
    midpointGrid h x y n 0 = x := by
  induction n with
  | zero => simp [midpointGrid]
  | succ n ih => exact (midpointGrid_even h x y n 0).trans ih

theorem midpointGrid_last (h : HasMetricMidpoints X) (x y : X) (n : ℕ) :
    midpointGrid h x y n (2 ^ n) = y := by
  induction n with
  | zero => simp [midpointGrid]
  | succ n ih => simpa only [pow_succ, Nat.mul_comm, midpointGrid_even] using ih

theorem midpointGrid_adjacent (h : HasMetricMidpoints X) (x y : X)
    (n : ℕ) {k : ℕ} (hk : k < 2 ^ n) :
    dist (midpointGrid h x y n k) (midpointGrid h x y n (k + 1)) ≤
      dist x y / (2 : ℝ) ^ n := by
  induction n generalizing k with
  | zero =>
      have : k = 0 := by simpa using hk
      simp [this, midpointGrid]
  | succ n ih =>
      have hkn : k / 2 < 2 ^ n := by
        rw [pow_succ] at hk
        omega
      have hbound := (div_le_div_of_nonneg_right (ih hkn) (by norm_num : (0 : ℝ) ≤ 2))
      have heq : dist x y / (2 : ℝ) ^ n / 2 = dist x y / (2 : ℝ) ^ (n + 1) := by
        rw [pow_succ, div_div]
      rw [heq] at hbound
      rcases Nat.mod_two_eq_zero_or_one k with heven | hodd
      · have heqk : k = 2 * (k / 2) := by omega
        rw [heqk, midpointGrid_even, midpointGrid_odd]
        exact (metricMidpoint_left h _ _).trans hbound
      · have heqk : k = 2 * (k / 2) + 1 := by omega
        have heqnext : k + 1 = 2 * (k / 2 + 1) := by omega
        have hg := midpointGrid_odd h x y n (k / 2)
        rw [← heqk] at hg
        rw [hg, heqnext, midpointGrid_even]
        exact (metricMidpoint_right h _ _).trans hbound

theorem midpointGrid_dist (h : HasMetricMidpoints X) (x y : X)
    (n : ℕ) {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ 2 ^ n) :
    dist (midpointGrid h x y n k) (midpointGrid h x y n l) ≤
      (l - k : ℕ) * (dist x y / (2 : ℝ) ^ n) := by
  induction l, hkl using Nat.le_induction with
  | base => simp
  | succ l hkl ih =>
      have hln : l < 2 ^ n := by omega
      have hdist := (dist_triangle (midpointGrid h x y n k)
        (midpointGrid h x y n l) (midpointGrid h x y n (l + 1))).trans
        (add_le_add (ih hln.le) (midpointGrid_adjacent h x y n hln))
      convert hdist using 1
      rw [show l + 1 - k = (l - k) + 1 by omega, Nat.cast_add, Nat.cast_one]
      ring

end PolycyclicRecognition

end

end OAI
