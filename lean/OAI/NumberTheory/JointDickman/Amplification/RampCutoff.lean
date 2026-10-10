import OAI.NumberTheory.JointDickman.Amplification.HighExclusiveThreshold
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

/-! # An averaged sharp cutoff for the coarse channel -/

namespace JointDickman

open MeasureTheory
open scoped NNReal

noncomputable def averagingRamp (a b x : ℝ) : ℝ :=
  (min b (max a x) - a) / (b - a)

theorem averagingRamp_bounds {a b : ℝ} (hab : a < b) (x : ℝ) :
    0 ≤ averagingRamp a b x ∧ averagingRamp a b x ≤ 1 := by
  have hlo : a ≤ min b (max a x) := le_min hab.le (le_max_left _ _)
  have hhi : min b (max a x) ≤ b := min_le_left _ _
  unfold averagingRamp
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) (sub_pos.mpr hab).le
  · apply (div_le_one (sub_pos.mpr hab)).mpr
    linarith

theorem averagingRamp_zero {a b x : ℝ} (hab : a < b) (hx : x ≤ a) :
    averagingRamp a b x = 0 := by simp [averagingRamp, max_eq_left hx, min_eq_right hab.le]

theorem averagingRamp_one {a b x : ℝ} (hab : a < b) (hx : b ≤ x) :
    averagingRamp a b x = 1 := by
  rw [averagingRamp, min_eq_left (hx.trans (le_max_right _ _))]
  exact div_self (sub_pos.mpr hab).ne'

open Classical in
theorem integral_strict_cutoff {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    (∫ t in a..b, if t < x then (1 : ℝ) else 0) = min b (max a x) - a := by
  have hae : (fun t : ℝ => if t < x then (1 : ℝ) else 0) =ᵐ[volume]
      (fun t : ℝ => if t ≤ x then (1 : ℝ) else 0) := by
    filter_upwards [volume.ae_ne x] with t ht
    have he : (t < x) ↔ t ≤ x := ⟨le_of_lt, fun h => lt_of_le_of_ne h ht⟩
    simp only [he]
  rw [intervalIntegral.integral_congr_ae (hae.mono (fun _ h _ => h))]
  by_cases hxa : x < a
  · have hi : (∫ t in a..b, if t ≤ x then (1 : ℝ) else 0) = 0 := by
      calc
        _ = ∫ _t in a..b, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_Ioo_of_le hab
          intro t ht
          exact ite_eq_right (by linarith [ht.1])
        _ = 0 := intervalIntegral.integral_zero
    rw [hi, max_eq_left hxa.le, min_eq_right hab, sub_self]
  · have hax := le_of_not_gt hxa
    by_cases hbx : b ≤ x
    · have hi : (∫ t in a..b, if t ≤ x then (1 : ℝ) else 0) = b - a := by
        calc
          _ = ∫ _t in a..b, (1 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro t ht
            have ht' : t ≤ b := (Set.uIcc_of_le hab ▸ ht).2
            exact ite_eq_left (ht'.trans hbx)
          _ = _ := by simp
      rw [hi, max_eq_right hax, min_eq_left hbx]
    · have hxb := le_of_not_ge hbx
      have h := intervalIntegral.integral_indicator (μ := volume) (f := fun _ : ℝ => (1 : ℝ))
        (show x ∈ Set.Icc a b from ⟨hax, hxb⟩)
      simpa [Set.indicator, max_eq_right hax, min_eq_right hxb] using h

open Classical in
theorem averagingRamp_integral {a b : ℝ} (hab : a < b) (x : ℝ) :
    averagingRamp a b x = (∫ t in a..b, if t < x then (1 : ℝ) else 0) / (b - a) := by
  rw [integral_strict_cutoff hab.le]
  rfl

theorem averagingRamp_lipschitz {a b : ℝ} (hab : a < b) :
    LipschitzWith ⟨1 / (b - a), by positivity⟩ (averagingRamp a b) := by
  have hclip := (LipschitzWith.id.const_max a).const_min b
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hc := hclip.dist_le_mul x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hc
  change |averagingRamp a b x - averagingRamp a b y| ≤ (1 / (b - a)) * |x - y|
  have heq : averagingRamp a b x - averagingRamp a b y =
      (min b (max a x) - min b (max a y)) / (b - a) := by unfold averagingRamp; ring
  rw [heq, abs_div, abs_of_pos (sub_pos.mpr hab), one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right hc (sub_pos.mpr hab).le

end JointDickman

end OAI
