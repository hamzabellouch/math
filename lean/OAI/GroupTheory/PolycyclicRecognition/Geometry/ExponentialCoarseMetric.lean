import OAI.GroupTheory.PolycyclicRecognition.Geometry.ContinuousFlowDistortion
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # Uniform coarse metric bounds for exponential lines -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable {V G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Group G] [MetricSpace G] [IsIsometricSMul G G]

/-- Continuity on one fixed unit ball and the one-parameter identity give
one uniform coarse metric bound for all exponential directions. -/
theorem continuous_radial_exponential_metric_bound
    (Exp : V → G) (hcont : Continuous Exp) (hzero : Exp 0 = 1)
    (hmul : ∀ v : V, ∀ s t : ℝ, Exp ((s + t) • v) = Exp (s • v) * Exp (t • v)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : V, dist 1 (Exp v) ≤ C * (1 + ‖v‖) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : V) 1).exists_bound_of_continuousOn
    ((continuous_const : Continuous (fun _ : V => (1 : G))).dist hcont).continuousOn
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  refine ⟨B, hB, ?_⟩
  intro v
  let n := ⌊‖v‖⌋₊ + 1
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_pos ⌊‖v‖⌋₊)
  have hvn : ‖v‖ ≤ (n : ℝ) := by simpa only [n, Nat.cast_add, Nat.cast_one] using
    (Nat.lt_floor_add_one ‖v‖).le
  have hnv : (n : ℝ) ≤ ‖v‖ + 1 := by
    have hh := Nat.floor_le (norm_nonneg v)
    dsimp [n]
    push_cast
    linarith
  let w := (n : ℝ)⁻¹ • v
  have hw : w ∈ closedBall (0 : V) 1 := by
    rw [mem_closedBall, dist_zero_right]
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    exact (inv_mul_le_iff₀ hn).mpr (by simpa using hvn)
  have hlocal : dist 1 (Exp w) ≤ B := by
    have hh := (hC w hw).trans (le_max_left C 0)
    simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using hh
  have hpow : ∀ k : ℕ, Exp ((k : ℝ) • w) = Exp w ^ k := by
    intro k
    induction k with
    | zero => simp [hzero]
    | succ k ih => rw [Nat.cast_succ, hmul, ih, one_smul, pow_succ]
  have hv : (n : ℝ) • w = v := by
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hn), one_smul]
  conv_lhs => rw [← hv, hpow n]
  apply (dist_one_pow_le _ _).trans
  calc
    _ ≤ (n : ℝ) * B := mul_le_mul_of_nonneg_left hlocal hn.le
    _ ≤ B * (1 + ‖v‖) := by nlinarith

/-- The same constant controls distances on every exponential line. -/
theorem continuous_radial_exponential_coarse_dist
    (Exp : V → G) (hcont : Continuous Exp) (hzero : Exp 0 = 1)
    (hmul : ∀ v : V, ∀ s t : ℝ, Exp ((s + t) • v) = Exp (s • v) * Exp (t • v)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : V) (s t : ℝ),
      dist (Exp (s • v)) (Exp (t • v)) ≤ C * ‖v‖ * |t - s| + C := by
  obtain ⟨C, hC, hb⟩ := continuous_radial_exponential_metric_bound Exp hcont hzero hmul
  refine ⟨C, hC, ?_⟩
  intro v s t
  have he : Exp (t • v) = Exp (s • v) * Exp ((t - s) • v) := by
    rw [← hmul]
    congr 1
    ring_nf
  rw [he]
  have hd : dist (Exp (s • v)) (Exp (s • v) * Exp ((t - s) • v)) =
      dist 1 (Exp ((t - s) • v)) := by
    simpa only [mul_one] using dist_mul_left (Exp (s • v)) (1 : G) (Exp ((t - s) • v))
  rw [hd]
  convert hb ((t - s) • v) using 1
  rw [norm_smul, Real.norm_eq_abs]
  ring

end PolycyclicRecognition

end

end OAI
