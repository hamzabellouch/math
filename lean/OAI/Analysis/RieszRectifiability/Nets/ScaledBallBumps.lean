import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.OpenPlaneBoxes
import OAI.Analysis.RieszRectifiability.Kernel.BoundedRegionTests

namespace OAI

/-!
Scaled ball bumps give compactly supported Lipschitz cutoffs. A lower ball-mass bound
allows normalization to integral one with an explicit scale-dependent Lipschitz bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

def scaledBallBump {d : ℕ} (a : Ambient d) (r : ℝ) (x : Ambient d) : ℝ :=
  max 0 (min 1 (2 - r⁻¹ * dist x a))

theorem scaledBallBump_bounds {d : ℕ} (a : Ambient d) (r : ℝ) (x : Ambient d) :
    0 ≤ scaledBallBump a r x ∧ scaledBallBump a r x ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem scaledBallBump_lipschitz {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    LipschitzWith (Real.toNNReal r⁻¹) (scaledBallBump a r) := by
  have h : LipschitzWith (Real.toNNReal r⁻¹)
      (fun x : Ambient d => r⁻¹ * dist x a) := by
    have heq : ‖r⁻¹‖₊ = Real.toNNReal r⁻¹ := by
      apply NNReal.coe_injective
      simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
        Real.coe_toNNReal r⁻¹ (inv_nonneg.mpr hr.le)]
    simpa only [mul_one, heq] using! lipschitz_const_mul_real (LipschitzWith.dist_left a) r⁻¹
  have hsub : LipschitzWith (Real.toNNReal r⁻¹)
      (fun x : Ambient d => 2 - r⁻¹ * dist x a) := by
    simpa only [zero_add] using! (LipschitzWith.const (2 : ℝ)).sub h
  exact (hsub.const_min 1).const_max 0

theorem scaledBallBump_eq_one {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (x : Ambient d) (hx : dist x a ≤ r) : scaledBallBump a r x = 1 := by
  have hb : r⁻¹ * dist x a ≤ 1 := by
    calc
      _ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hr.le)
      _ = 1 := inv_mul_cancel₀ hr.ne'
  simp only [scaledBallBump, min_eq_left (by linarith : (1 : ℝ) ≤ 2 - r⁻¹ * dist x a),
    max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem scaledBallBump_support_bound {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (x : Ambient d) (hx : scaledBallBump a r x ≠ 0) : dist x a ≤ 2 * r := by
  by_contra hn
  have hdist : 2 * r < dist x a := lt_of_not_ge hn
  have hb : 2 < r⁻¹ * dist x a := by
    calc
      (2 : ℝ) = r⁻¹ * (2 * r) := by field_simp
      _ < _ := mul_lt_mul_of_pos_left hdist (inv_pos.mpr hr)
  exact hx (max_eq_left ((min_le_right _ _).trans (by linarith : 2 - r⁻¹ * dist x a ≤ 0)))

theorem scaledBallBump_hasCompactSupport {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (scaledBallBump a r) := by
  apply HasCompactSupport.intro (isCompact_closedBall a (2 * r))
  intro x hx
  by_contra hn
  exact hx (scaledBallBump_support_bound a r hr x hn)

theorem scaledBallBump_integral_lower {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    μ.real (ball a r) ≤ ∫ x, scaledBallBump a r x ∂μ := by
  have hi := (scaledBallBump_lipschitz a r hr).continuous.integrable_of_hasCompactSupport
    (μ := μ) (scaledBallBump_hasCompactSupport a r hr)
  have hs : (∫ x in ball a r, scaledBallBump a r x ∂μ) = μ.real (ball a r) := by
    calc
      _ = ∫ _x in ball a r, (1 : ℝ) ∂μ := by
        apply setIntegral_congr_fun measurableSet_ball
        intro x hx
        exact scaledBallBump_eq_one a r hr x hx.le
      _ = _ := by simp only [setIntegral_const, smul_eq_mul, mul_one]
  rw [← hs]
  exact setIntegral_le_integral hi (Eventually.of_forall fun x => (scaledBallBump_bounds a r x).1)

theorem exists_normalized_ball_bump {d : ℕ} (n : ℕ) (C c : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ) (hc : 0 < c)
    (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (hmass : ENNReal.ofReal (c * r ^ n) ≤ μ (ball a r)) :
    ∃ (φ : Ambient d → ℝ) (L : ℝ≥0),
      HasCompactSupport φ ∧ LipschitzWith L φ ∧
      (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≠ 0 → dist x a ≤ 2 * r) ∧
      (∫ x, φ x ∂μ) = 1 ∧ (L : ℝ) ≤ (c * r ^ (n + 1))⁻¹ := by
  let := hg.finite_on_compacts
  let b := scaledBallBump a r
  let M := ∫ x, b x ∂μ
  have hfinite : μ (ball a r) ≠ ∞ :=
    ((hg.2 a r hr).trans_lt ENNReal.ofReal_lt_top).ne
  have hl : c * r ^ n ≤ M := by
    have ht := ENNReal.toReal_mono hfinite hmass
    rw [ENNReal.toReal_ofReal (by positivity)] at ht
    exact ht.trans (scaledBallBump_integral_lower μ a r hr)
  have hM : 0 < M := (mul_pos hc (pow_pos hr n)).trans_le hl
  let φ := fun x => M⁻¹ * b x
  let L : ℝ≥0 := ‖M⁻¹‖₊ * Real.toNNReal r⁻¹
  refine ⟨φ, L, (scaledBallBump_hasCompactSupport a r hr).mul_left,
    lipschitz_const_mul_real (scaledBallBump_lipschitz a r hr) M⁻¹, ?_, ?_, ?_, ?_⟩
  · intro x
    exact mul_nonneg (inv_nonneg.mpr hM.le) (scaledBallBump_bounds a r x).1
  · intro x hx
    apply scaledBallBump_support_bound a r hr x
    intro hb
    exact hx (by simp only [φ, b, hb, mul_zero])
  · change (∫ x, M⁻¹ * b x ∂μ) = 1
    rw [integral_const_mul]
    exact inv_mul_cancel₀ hM.ne'
  · change ((‖M⁻¹‖₊ : ℝ) * (Real.toNNReal r⁻¹ : ℝ)) ≤ _
    rw [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM),
      Real.coe_toNNReal r⁻¹ (inv_nonneg.mpr hr.le)]
    calc
      _ ≤ (c * r ^ n)⁻¹ * r⁻¹ := mul_le_mul_of_nonneg_right
        (by simpa only [one_div] using! one_div_le_one_div_of_le (by positivity : 0 < c * r ^ n) hl)
        (inv_nonneg.mpr hr.le)
      _ = _ := by rw [pow_succ, ← mul_assoc, mul_inv_rev]; ring

end

end RieszRectifiability

end OAI
