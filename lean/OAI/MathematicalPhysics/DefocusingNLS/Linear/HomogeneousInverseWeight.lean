import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousYSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

namespace OAI

/-! # Integrability of the inverse homogeneous Fourier weight

The low-frequency exponent is strictly below dimension twelve and the
high-frequency exponent is strictly above it. This is the continuous
counterpart of the checked expanding-torus inverse-weight sum.
-/

open MeasureTheory

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem homogeneousFourierWeight_inv_bound (a k : ℝ) (ξ : E) (hξ : ξ ≠ 0)
    (s : ℝ) (hs : s = 6 - a ∨ s = k) :
    (homogeneousFourierWeight a k ξ)⁻¹ ≤
      (2 * Real.pi) ^ (12 : ℕ) * ‖ξ‖ ^ (-(2 * s)) := by
  have hlow : 0 < ((2 * Real.pi) ^ (12 : ℕ))⁻¹ * ‖ξ‖ ^ (2 * s) := by
    exact mul_pos (by positivity) (Real.rpow_pos_of_pos (norm_pos_iff.mpr hξ) _)
  have hle : ((2 * Real.pi) ^ (12 : ℕ))⁻¹ * ‖ξ‖ ^ (2 * s) ≤
      homogeneousFourierWeight a k ξ := by
    rcases hs with rfl | rfl
    · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)
    · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)
  calc
    _ ≤ (((2 * Real.pi) ^ (12 : ℕ))⁻¹ * ‖ξ‖ ^ (2 * s))⁻¹ := inv_anti₀ hlow hle
    _ = _ := by rw [mul_inv_rev, inv_inv, Real.rpow_neg (norm_nonneg ξ)]; ring

/-- The inverse of the exact Y Fourier weight is integrable over all frequencies. -/
theorem integrable_homogeneousFourierWeight_inv (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    Integrable (fun ξ => (homogeneousFourierWeight a k ξ)⁻¹) := by
  have hm : AEStronglyMeasurable (fun ξ => (homogeneousFourierWeight a k ξ)⁻¹) volume :=
    (continuous_homogeneousFourierWeight a k ha1 hk).measurable.inv.aestronglyMeasurable
  have hn : ∀ᵐ ξ : E ∂volume, ξ ≠ 0 := by
    simp only [ae_iff, not_not, Set.ofPred_eq_eq_singleton]
    exact measure_singleton _
  have hsmall : IntegrableOn (fun ξ => (homogeneousFourierWeight a k ξ)⁻¹)
      (Metric.ball (0 : E) 1) := by
    apply integrableOn_ball_of_norm_le_rpow (by norm_num : 1 ≤ Module.finrank ℝ E)
      (α := 2 * (6 - a)) (C := (2 * Real.pi) ^ (12 : ℕ)) (by norm_num; linarith)
      ?_ hm
    filter_upwards [ae_restrict_of_ae hn] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (homogeneousFourierWeight_nonneg a k ξ))]
    exact homogeneousFourierWeight_inv_bound a k ξ hξ (6 - a) (Or.inl rfl)
  have hbase : Integrable (fun ξ : E => (1 + ‖ξ‖) ^ (-(2 * k))) := by
    apply integrable_one_add_norm
    norm_num
    linarith
  have hlarge : IntegrableOn (fun ξ => (homogeneousFourierWeight a k ξ)⁻¹)
      (Metric.ball (0 : E) 1)ᶜ := by
    apply ((hbase.const_mul ((2 * Real.pi) ^ (12 : ℕ) * 2 ^ (2 * k))).integrableOn).mono'
      hm.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with ξ hξ
    have hr : 1 ≤ ‖ξ‖ := by simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hξ
    have hn0 : ξ ≠ 0 := by intro hz; simp only [hz, norm_zero] at hr; linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (homogeneousFourierWeight_nonneg a k ξ))]
    calc
      _ ≤ (2 * Real.pi) ^ (12 : ℕ) * ‖ξ‖ ^ (-(2 * k)) :=
        homogeneousFourierWeight_inv_bound a k ξ hn0 k (Or.inr rfl)
      _ ≤ (2 * Real.pi) ^ (12 : ℕ) * (((1 + ‖ξ‖) / 2) ^ (-(2 * k))) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos
            (show 0 < (1 + ‖ξ‖) / 2 by positivity)
            (show (1 + ‖ξ‖) / 2 ≤ ‖ξ‖ by linarith)
            (show -(2 * k) ≤ 0 by linarith)) (by positivity)
      _ = _ := by
        rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2),
          div_inv_eq_mul]
        ring
  have hu := hsmall.union hlarge
  simpa only [Set.union_compl_self, integrableOn_univ] using hu

end DefocusingNLS

end OAI
