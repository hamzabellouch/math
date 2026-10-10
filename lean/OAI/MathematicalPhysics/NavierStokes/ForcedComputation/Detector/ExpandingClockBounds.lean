import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateClock
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace OAI

/-! All clock derivatives have bounds independent of their starting time.
The only scaling factor is the reciprocal transition duration. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Set
open scoped ContDiff Topology

theorem unitPulse_compact : HasCompactSupport (smoothPulse 0 1) := by
  apply HasCompactSupport.intro (K := Icc (0 : ℝ) 1) isCompact_Icc
  intro t ht
  by_cases h : t ≤ 0
  · exact smoothPulse_before (by norm_num) h
  · exact smoothPulse_after (by norm_num) (by
      have := not_and_or.mp ht
      rcases this with h0 | h1
      · exact False.elim (h0 (le_of_lt (lt_of_not_ge h)))
      · exact le_of_lt (lt_of_not_ge h1))

theorem unitRamp_jet_bound (m : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ i ≤ m, ∀ t, |iteratedDeriv i (smoothRamp 0 1) t| ≤ C := by
  obtain ⟨B, _, hB⟩ := unitPulse_compact.exists_bound_iteratedFDeriv
    (smoothPulse_smooth 0 1) m
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro i hi t
  cases i with
  | zero =>
    simpa only [iteratedDeriv_zero, abs_of_nonneg (smoothRamp_range 0 1 t).1] using
      (smoothRamp_range 0 1 t).2.trans (le_max_left 1 B)
  | succ i =>
    rw [iteratedDeriv_succ']
    have hb := hB i (by omega) t
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hb
    exact hb.trans (le_max_right _ _)

theorem smoothRamp_iteratedDeriv_scale (a b t : ℝ) (n : ℕ) :
    iteratedDeriv n (smoothRamp a b) t =
      (b - a)⁻¹ ^ n * iteratedDeriv n (smoothRamp 0 1) ((b - a)⁻¹ * (t - a)) := by
  have he : smoothRamp a b =
      fun t => smoothRamp 0 1 ((b - a)⁻¹ * (t - a)) := by
    funext t
    simp only [smoothRamp, sub_zero, div_eq_mul_inv, inv_one, mul_one]
    rw [mul_comm]
  rw [he]
  have hshift := congrFun (iteratedDeriv_comp_sub_const (n := n)
    (f := fun u => smoothRamp 0 1 ((b - a)⁻¹ * u)) (s := a)) t
  have hscale := congrFun (iteratedDeriv_comp_const_mul (n := n)
    ((smoothRamp_smooth 0 1).of_le (by simp)) ((b - a)⁻¹)) (t - a)
  exact hshift.trans hscale

theorem smoothRamp_derivative_bound {C : ℝ} {m : ℕ}
    (hC : ∀ i ≤ m, ∀ t, |iteratedDeriv i (smoothRamp 0 1) t| ≤ C)
    (a b t : ℝ) {n : ℕ} (hn : n ≤ m) :
    |iteratedDeriv n (smoothRamp a b) t| ≤ |(b - a)⁻¹| ^ n * C := by
  rw [smoothRamp_iteratedDeriv_scale, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (hC n hn _) (pow_nonneg (abs_nonneg _) n)

end ForcedComputation.ExpandingDetector

end

end OAI
