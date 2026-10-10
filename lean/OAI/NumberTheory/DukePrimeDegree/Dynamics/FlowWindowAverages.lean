import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Dynamics.BirkhoffSum.Average

namespace OAI

/-!
# Unit smoothing and continuous orbit windows

Discrete averages of a unit-smoothed observable are exactly continuous
flow averages at integer lengths. Shifting the initial point changes
only two boundary intervals; their contribution is uniformly bounded.
Neither statement assumes that a time-one map is ergodic.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree

variable {X : Type*}

def unitFlowSmooth (U : ℝ → X → X) (f : X → ℝ) (x : X) : ℝ :=
  ∫ t in (0 : ℝ)..1, f (U t x)

lemma flow_nat_iterate (U : ℝ → X → X)
    (hzero : ∀ x, U 0 x = x)
    (hadd : ∀ s t x, U (s + t) x = U s (U t x)) (N : ℕ) (x : X) :
    (U 1)^[N] x = U (N : ℝ) x := by
  induction N with
  | zero => simpa using (hzero x).symm
  | succ N ih =>
      rw [Function.iterate_succ_apply', ih, Nat.cast_succ]
      rw [add_comm, hadd]

lemma unitFlowSmooth_nat (U : ℝ → X → X) (f : X → ℝ)
    (hadd : ∀ s t x, U (s + t) x = U s (U t x)) (N : ℕ) (x : X) :
    unitFlowSmooth U f (U (N : ℝ) x) =
      ∫ t in (N : ℝ)..(N : ℝ) + 1, f (U t x) := by
  unfold unitFlowSmooth
  simp_rw [← hadd]
  rw [intervalIntegral.integral_comp_add_right (fun t => f (U t x)) (N : ℝ)]
  simp only [zero_add, add_comm (1 : ℝ)]

/-- Integer discrete averages of the smoothed observable are literal
continuous-time averages of the original observable. -/
theorem birkhoffAverage_unitFlowSmooth
    (U : ℝ → X → X) (f : X → ℝ)
    (hzero : ∀ x, U 0 x = x)
    (hadd : ∀ s t x, U (s + t) x = U s (U t x))
    (hint : ∀ x a b, IntervalIntegrable (fun t => f (U t x)) volume a b)
    (N : ℕ) (x : X) :
    birkhoffAverage ℝ (U 1) (unitFlowSmooth U f) N x =
      (N : ℝ)⁻¹ * ∫ t in (0 : ℝ)..(N : ℝ), f (U t x) := by
  unfold birkhoffAverage birkhoffSum
  simp only [smul_eq_mul]
  congr 1
  simp_rw [flow_nat_iterate U hzero hadd, unitFlowSmooth_nat U f hadd]
  simpa only [Nat.cast_zero, Nat.cast_succ] using
    (intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ))
      (n := N) (f := fun t => f (U t x)) (fun k _ => by
        simpa only [Nat.cast_add, Nat.cast_one] using hint x k (k + 1)))

/-- A translated window differs by two boundary intervals of the
translation length, regardless of the total window length. -/
theorem integral_window_shift_bound (F : ℝ → ℝ)
    (hint : ∀ a b, IntervalIntegrable F volume a b)
    (C : ℝ) (hC : ∀ t, |F t| ≤ C) (s L : ℝ) :
    |(∫ t in s..s + L, F t) - ∫ t in (0 : ℝ)..L, F t| ≤ 2 * C * |s| := by
  rw [intervalIntegral.integral_interval_sub_interval_comm'
    (hint s (s + L)) (hint 0 L) (hint s 0)]
  have hright : |∫ t in L..s + L, F t| ≤ C * |s| := by
    simpa only [Real.norm_eq_abs, add_sub_cancel_right] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (f := F)
        (a := L) (b := s + L) (C := C) (fun t _ => by simpa using hC t))
  have hleft : |∫ t in (0 : ℝ)..s, F t| ≤ C * |s| := by
    simpa only [Real.norm_eq_abs, sub_zero] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (f := F)
        (a := 0) (b := s) (C := C) (fun t _ => by simpa using hC t))
  calc
    _ ≤ |∫ t in L..s + L, F t| + |∫ t in (0 : ℝ)..s, F t| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le
        (∫ t in L..s + L, F t) (∫ t in (0 : ℝ)..s, F t)
    _ ≤ C * |s| + C * |s| := add_le_add hright hleft
    _ = _ := by ring

/-- Invariance of the eventual average is under every real flow time,
not just under its integer subgroup. -/
theorem birkhoffAverage_unitFlowSmooth_shift_bound
    (U : ℝ → X → X) (f : X → ℝ)
    (hzero : ∀ x, U 0 x = x)
    (hadd : ∀ s t x, U (s + t) x = U s (U t x))
    (hint : ∀ x a b, IntervalIntegrable (fun t => f (U t x)) volume a b)
    (C : ℝ) (hC : ∀ x, |f x| ≤ C) (N : ℕ) (s : ℝ) (x : X) :
    |birkhoffAverage ℝ (U 1) (unitFlowSmooth U f) N (U s x) -
        birkhoffAverage ℝ (U 1) (unitFlowSmooth U f) N x| ≤
      (N : ℝ)⁻¹ * (2 * C * |s|) := by
  rw [birkhoffAverage_unitFlowSmooth U f hzero hadd hint,
    birkhoffAverage_unitFlowSmooth U f hzero hadd hint, ← mul_sub, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  simp_rw [← hadd]
  rw [intervalIntegral.integral_comp_add_right (fun t => f (U t x)) s]
  simp only [zero_add]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  simpa only [add_comm (N : ℝ)] using
    integral_window_shift_bound (fun t => f (U t x)) (hint x) C (fun t => hC (U t x)) s N

end DukePrimeDegree

end

end OAI
