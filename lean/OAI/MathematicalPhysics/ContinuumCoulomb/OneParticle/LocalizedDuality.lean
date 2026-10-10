import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedLeakage

namespace OAI

/-! Actual compact local dual tests: a common positive diagonal mass,
disjoint supports and exponentially small off-site pairings. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

def localizedTest (χ : Position → ℝ) (u : PlanarPosition) (x : Position) : ℝ :=
  χ (x - planarCenter u)

theorem localizedTest_smooth {χ : Position → ℝ} (hχ : ContDiff ℝ ∞ χ) (u : PlanarPosition) :
    ContDiff ℝ ∞ (localizedTest χ u) := hχ.comp (contDiff_id.sub contDiff_const)

theorem localizedTest_hasCompactSupport {χ : Position → ℝ} (hc : HasCompactSupport χ)
    (u : PlanarPosition) : HasCompactSupport (localizedTest χ u) :=
  hc.comp_homeomorph (Homeomorph.subRight (planarCenter u))

theorem localizedTest_support {χ : Position → ℝ} {R : ℝ}
    (hs : tsupport χ ⊆ Metric.closedBall 0 R) (u : PlanarPosition) :
    tsupport (localizedTest χ u) ⊆ Metric.closedBall (planarCenter u) R := by
  apply closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  have hχx : χ (x - planarCenter u) ≠ 0 := hx
  have h := hs (subset_tsupport χ hχx)
  simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using h

theorem localizedTest_disjoint {χ : Position → ℝ} {R : ℝ}
    (hs : tsupport χ ⊆ Metric.closedBall 0 R) (u v : PlanarPosition)
    (hsep : 2 * R < ‖u - v‖) : Disjoint (tsupport (localizedTest χ u)) (tsupport (localizedTest χ v)) := by
  apply Set.disjoint_left.mpr
  intro x hxu hxv
  have hu := localizedTest_support hs u hxu
  have hv := localizedTest_support hs v hxv
  simp only [Metric.mem_closedBall, dist_eq_norm] at hu hv
  have h : ‖planarCenter u - planarCenter v‖ ≤ ‖planarCenter u - x‖ + ‖x - planarCenter v‖ := by
    simpa only [dist_eq_norm] using dist_triangle (planarCenter u) x (planarCenter v)
  rw [norm_sub_rev (planarCenter u) x, planarCenter_norm_sub] at h
  linarith

def localizedDualPair (freq : ℝ) (u v : PlanarPosition) (χ : Position → ℝ) : ℝ :=
  ∫ x, localizedDensity freq u x * localizedTest χ v x

theorem localizedDualPair_diagonal (freq : ℝ) (u : PlanarPosition) (χ : Position → ℝ) :
    localizedDualPair freq u u χ = ∫ x, localizedDensity freq 0 x * χ x := by
  unfold localizedDualPair localizedTest
  rw [← integral_add_right_eq_self
    (fun x => localizedDensity freq u x * χ (x - planarCenter u)) (planarCenter u)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [localizedDensity_translate freq u, add_sub_cancel_right]

theorem localizedDualPair_diagonal_positive {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) {χ : Position → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hn : ∀ x, 0 ≤ χ x) (h0 : 0 < χ 0) : 0 < localizedDualPair freq u u χ := by
  rw [localizedDualPair_diagonal]
  exact integral_pos_of_integrable_nonneg_nonzero
    ((localizedDensity_continuous freq 0).mul hχ)
    (((localizedDensity_continuous freq 0).mul hχ).integrable_of_hasCompactSupport hc.mul_left)
    (fun x => mul_nonneg (localizedDensity_nonnegative freq 0 x) (hn x))
    (mul_pos (localizedDensity_positive hfreq 0 0) h0).ne'

theorem localizedDualPair_offsite {freq R : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) {χ : Position → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Metric.closedBall 0 R) (hsep : R + 1 ≤ ‖u - v‖) :
    |localizedDualPair freq u v χ| ≤
      (localizedTailConstant freq * Real.exp (R - ‖u - v‖)) * (∫ x, |χ x|) := by
  have hpt (x : Position) : ‖localizedDensity freq u (x + planarCenter v) * χ x‖ ≤
      (localizedTailConstant freq * Real.exp (R - ‖u - v‖)) * |χ x| := by
    by_cases hx : χ x = 0
    · simp only [hx, mul_zero, norm_zero, abs_zero, le_refl]
    have hn : ‖x‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hs (subset_tsupport χ hx)
    have hb := localizedDensity_near_other_center hfreq u v (x + planarCenter v)
      (by simpa only [add_sub_cancel_right] using hn) hsep
    rw [norm_mul, Real.norm_of_nonneg (localizedDensity_nonnegative freq u _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  unfold localizedDualPair localizedTest
  rw [← integral_add_right_eq_self
    (fun x => localizedDensity freq u x * χ (x - planarCenter v)) (planarCenter v)]
  simp only [add_sub_cancel_right]
  have h := norm_integral_le_of_norm_le
    (f := fun x => localizedDensity freq u (x + planarCenter v) * χ x)
    ((hχ.integrable_of_hasCompactSupport (μ := volume) hc).norm.const_mul
      (localizedTailConstant freq * Real.exp (R - ‖u - v‖)))
    (Filter.Eventually.of_forall hpt)
  simpa only [integral_const_mul, Real.norm_eq_abs] using h

end ContinuumCoulomb

end

end OAI
