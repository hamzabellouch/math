import OAI.GroupTheory.PolycyclicRecognition.Algebra.LogDistortion
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.MetricSpace.ProperSpace

namespace OAI

/-! # Continuous contracting flows

The local metric bounds in logarithmic distortion follow from continuity
and compactness. A continuous one-parameter homomorphism has at most linear
metric growth, so no differentiability estimate needs to be assumed here.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

variable {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

theorem dist_one_pow_le (g : G) (n : ℕ) : dist 1 (g ^ n) ≤ (n : ℝ) * dist 1 g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    calc
      dist 1 (g ^ n * g) ≤ dist 1 (g ^ n) + dist 1 g := dist_one_mul_le _ _
      _ ≤ (n : ℝ) * dist 1 g + dist 1 g := add_le_add ih le_rfl
      _ = _ := by push_cast; ring

/-- Every continuous one-parameter homomorphism has a linear metric bound
for times at least one, using only boundedness of its compact unit interval. -/
theorem continuous_flow_linear_growth
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t, 1 ≤ t → dist 1 (d t) ≤ L * t := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (continuous_const.dist hd).continuousOn
  have hC0 : 0 ≤ C := by
    have h := hC (mem_image_of_mem (fun t => dist (1 : G) (d t))
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num))
    simpa [hd0] using h
  have hpower (s : ℝ) (n : ℕ) : d ((n : ℝ) * s) = d s ^ n := by
    induction n with
    | zero => simp [hd0]
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hmul, ih, pow_succ]
  refine ⟨2 * C, by positivity, fun t ht => ?_⟩
  let n := ⌊t⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have htn : t ≤ (n : ℝ) := by simpa [n] using (Nat.lt_floor_add_one t).le
  have hnt : (n : ℝ) ≤ t + 1 := by
    simpa [n] using add_le_add_right (Nat.floor_le (by linarith : 0 ≤ t)) 1
  have hs : t / n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith) hnr.le, (div_le_one hnr).mpr htn⟩
  have hlocal : dist 1 (d (t / n)) ≤ C := hC (mem_image_of_mem _ hs)
  have heq : d t = d (t / n) ^ n := by
    convert hpower (t / n) n using 1
    field_simp
  calc
    dist 1 (d t) = dist 1 (d (t / n) ^ n) := congrArg (dist 1) heq
    _ ≤ (n : ℝ) * dist 1 (d (t / n)) := dist_one_pow_le _ _
    _ ≤ (n : ℝ) * C := mul_le_mul_of_nonneg_left hlocal hnr.le
    _ ≤ (2 * C) * t := by nlinarith

/-- For a continuous exponential chart and continuous contracting flow,
polynomially corrected contraction implies an actual logarithmic distance bound.
The compact unit-ball bound and the flow-length bound are derived in the proof. -/
theorem logarithmic_distortion_of_continuous_flow
    {V : Type*} [NormedAddCommGroup V] [ProperSpace V]
    (Exp : V → G) (hExp : Continuous Exp)
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t) (T : ℝ → V → V)
    {C : ℝ} (hC : 0 ≤ C) (b : ℕ)
    (hconj : ∀ v t, 0 ≤ t → Exp v = d t * Exp (T t v) * (d t)⁻¹)
    (hcontract : ∀ v t, 0 ≤ t → ‖T t v‖ ≤ C * (1 + t) ^ b * Real.exp (-t) * ‖v‖) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  obtain ⟨L, hL, hpath⟩ := continuous_flow_linear_growth d hd hd0 hmul
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : V) 1).bddAbove_image
    (continuous_const.dist hExp).continuousOn
  have hB0 : 0 ≤ B := (dist_nonneg (x := (1 : G)) (y := Exp 0)).trans
    (hB (mem_image_of_mem _ (by simp : (0 : V) ∈ closedBall 0 1)))
  apply logarithmic_distortion_of_contracting_flow Exp d T hC hL hB0 b hconj hcontract hpath
  intro v hv
  apply hB
  exact mem_image_of_mem _ (by simpa only [mem_closedBall, dist_zero_right] using hv)

end PolycyclicRecognition

end

end OAI
