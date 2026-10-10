import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousAnnulusBounds
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace OAI

/-! # A concrete smooth dyadic partition in twelve dimensions -/

open Filter
open scoped SchwartzMap Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousCoreBump : ContDiffBump (0 : E) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

noncomputable def homogeneousCoreCutoff : 𝓢(E, ℂ) :=
  (homogeneousCoreBump.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp homogeneousCoreBump.contDiff)

@[simp] theorem homogeneousCoreCutoff_apply (x : E) :
    homogeneousCoreCutoff x = (homogeneousCoreBump x : ℂ) := rfl

theorem homogeneousCoreCutoff_hasCompactSupport :
    HasCompactSupport (homogeneousCoreCutoff : E → ℂ) :=
  homogeneousCoreBump.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)

theorem homogeneousCoreCutoff_one (x : E) (hx : ‖x‖ ≤ 1 / 2) :
    homogeneousCoreCutoff x = 1 := by
  rw [homogeneousCoreCutoff_apply, homogeneousCoreBump.one_of_mem_closedBall]
  · simp
  · simpa [homogeneousCoreBump, Metric.mem_closedBall, dist_zero_right] using hx

theorem homogeneousCoreCutoff_zero (x : E) (hx : 1 ≤ ‖x‖) :
    homogeneousCoreCutoff x = 0 := by
  rw [homogeneousCoreCutoff_apply, homogeneousCoreBump.zero_of_le_dist]
  · simp
  · simpa [homogeneousCoreBump, dist_zero_right] using hx

noncomputable def homogeneousHalfScale : E ≃L[ℝ] E :=
  (Units.mk0 (1 / 2 : ℝ) (by norm_num)) • ContinuousLinearEquiv.refl ℝ E

@[simp] theorem homogeneousHalfScale_apply (x : E) :
    homogeneousHalfScale x = (1 / 2 : ℝ) • x := rfl

noncomputable def homogeneousAnnulusCutoff : 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ homogeneousHalfScale homogeneousCoreCutoff -
    homogeneousCoreCutoff

@[simp] theorem homogeneousAnnulusCutoff_apply (x : E) :
    homogeneousAnnulusCutoff x = homogeneousCoreCutoff ((1 / 2 : ℝ) • x) -
      homogeneousCoreCutoff x := by
  simp [homogeneousAnnulusCutoff]

theorem homogeneousAnnulusCutoff_hasCompactSupport :
    HasCompactSupport (homogeneousAnnulusCutoff : E → ℂ) := by
  exact (homogeneousCoreCutoff_hasCompactSupport.comp_homeomorph
    homogeneousHalfScale.toHomeomorph).sub homogeneousCoreCutoff_hasCompactSupport

theorem homogeneousAnnulusCutoff_support :
    ∀ x ∈ tsupport (homogeneousAnnulusCutoff : E → ℂ),
      (1 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2 := by
  apply closure_minimal ?_ ((isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const))
  intro x hx
  constructor
  · by_contra h
    change ¬ (1 / 2 : ℝ) ≤ ‖x‖ at h
    have hs : ‖x‖ ≤ 1 / 2 := (lt_of_not_ge h).le
    have hs' : ‖(1 / 2 : ℝ) • x‖ ≤ 1 / 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      norm_num
      linarith [norm_nonneg x]
    exact hx (by
      rw [homogeneousAnnulusCutoff_apply, homogeneousCoreCutoff_one ((1 / 2 : ℝ) • x) hs',
        homogeneousCoreCutoff_one x hs, sub_self])
  · by_contra h
    change ¬ ‖x‖ ≤ (2 : ℝ) at h
    have hs : 1 ≤ ‖x‖ := by linarith [lt_of_not_ge h]
    have hs' : 1 ≤ ‖(1 / 2 : ℝ) • x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      norm_num
      linarith [lt_of_not_ge h]
    exact hx (by
      rw [homogeneousAnnulusCutoff_apply, homogeneousCoreCutoff_zero ((1 / 2 : ℝ) • x) hs',
        homogeneousCoreCutoff_zero x hs, sub_self])

theorem homogeneousCoreCutoff_dyadic_tendsto_one (y : E) :
    Tendsto (fun n : ℕ => homogeneousCoreCutoff (((2 : ℝ) ^ n)⁻¹ • y)) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ • y) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    simpa only [inv_pow, zero_smul] using hp.smul_const y
  have hc := homogeneousCoreCutoff.continuous.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, homogeneousCoreCutoff_one 0 (by simp)] using hc

theorem homogeneousAnnulusCutoff_dyadic_eventually_zero (y : E) :
    ∀ᶠ n : ℕ in atTop, homogeneousAnnulusCutoff (((2 : ℝ) ^ n)⁻¹ • y) = 0 := by
  have ht : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ • y) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    simpa only [inv_pow, zero_smul] using hp.smul_const y
  have he : ∀ᶠ x : E in 𝓝 0, homogeneousAnnulusCutoff x = 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
    have hslt : ‖x‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hx
    have hs : ‖x‖ ≤ 1 / 2 := hslt.le
    have hs' : ‖(1 / 2 : ℝ) • x‖ ≤ 1 / 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      norm_num
      linarith [norm_nonneg x]
    rw [homogeneousAnnulusCutoff_apply, homogeneousCoreCutoff_one ((1 / 2 : ℝ) • x) hs',
      homogeneousCoreCutoff_one x hs, sub_self]
  exact ht.eventually he

theorem homogeneousAnnulusCutoff_dyadic_sum (y : E) :
    HasSum (fun n : ℕ => homogeneousAnnulusCutoff (((2 : ℝ) ^ n)⁻¹ • y))
      (1 - homogeneousCoreCutoff y) := by
  have hz := homogeneousAnnulusCutoff_dyadic_eventually_zero y
  have hs : Summable (fun n : ℕ =>
      ‖homogeneousAnnulusCutoff (((2 : ℝ) ^ n)⁻¹ • y)‖) := by
    apply Summable.of_norm_bounded_eventually_nat (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    filter_upwards [hz] with n hn
    simp [hn]
  apply (hasSum_iff_tendsto_nat_of_summable_norm hs).mpr
  have hpartial (n : ℕ) :
      ∑ j ∈ Finset.range n, homogeneousAnnulusCutoff (((2 : ℝ) ^ j)⁻¹ • y) =
        homogeneousCoreCutoff (((2 : ℝ) ^ n)⁻¹ • y) - homogeneousCoreCutoff y := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, homogeneousAnnulusCutoff_apply]
      have he : (1 / 2 : ℝ) • (((2 : ℝ) ^ n)⁻¹ • y) = ((2 : ℝ) ^ (n + 1))⁻¹ • y := by
        rw [smul_smul, pow_succ, mul_inv_rev]
        norm_num
      rw [he]
      ring
  simp_rw [hpartial]
  exact (homogeneousCoreCutoff_dyadic_tendsto_one y).sub_const _

end DefocusingNLS

end OAI
