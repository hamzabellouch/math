import OAI.NumberTheory.JointDickman.Amplification.SingleViolationBounds

namespace OAI

/-! # A power saving in the one-coefficient sieve remainder -/

namespace JointDickman

open Filter
open scoped Topology

theorem single_coefficient_remainder_power {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ B : ℕ in atTop, ∀ H : ℝ, Real.exp (δ * B) ≤ H →
      singleCoefficientRemainder B (sieveCutoff (δ / 8) B) ≤ H / (B : ℝ)^10 := by
  have hlim : Tendsto (fun B : ℕ => 4 * ((B : ℝ)^11 / Real.exp ((3 * δ / 4) * B)))
      atTop (𝓝 0) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 11 (by linarith : 0 < 3 * δ / 4)).tendsto_div_nhds_zero
    simpa only [Function.comp_def, mul_zero] using (h.comp tendsto_natCast_atTop_atTop).const_mul 4
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    coefficientScale_eventually_le, sieveCutoff_eventually (by linarith : 0 < δ / 8),
    eventually_gt_atTop 0] with B hsmall hscale hcut hB
  intro H hH
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hF : 1 ≤ Real.exp ((δ / 8) * B) := Real.one_le_exp_iff.mpr (mul_nonneg (by linarith) hB0.le)
  have hZ0 : (0 : ℝ) ≤ sieveCutoff (δ / 8) B := Nat.cast_nonneg _
  have hZplus : (sieveCutoff (δ / 8) B + 1 : ℝ) ≤ 2 * Real.exp ((δ / 8) * B) := by
    linarith only [hcut.2.2.2, hF]
  have hbound : singleCoefficientRemainder B (sieveCutoff (δ / 8) B) ≤
      4 * (B : ℝ) * Real.exp ((δ / 4) * B) := by
    calc
      _ ≤ (B : ℝ) * (2 * (2 * Real.exp ((δ / 8) * B)) * Real.exp ((δ / 8) * B)) := by
        unfold singleCoefficientRemainder
        apply mul_le_mul hscale _ (by positivity) hB0.le
        gcongr
        exact hcut.2.2.2
      _ = _ := by
        rw [show (δ / 4) * (B : ℝ) = (δ / 8) * B + (δ / 8) * B by ring, Real.exp_add]
        ring
  have hsmall' : 4 * (B : ℝ)^11 ≤ Real.exp ((3 * δ / 4) * B) := by
    apply (div_le_one (Real.exp_pos _)).mp
    convert hsmall using 1
    ring
  have htotal : (4 * (B : ℝ) * Real.exp ((δ / 4) * B)) * (B : ℝ)^10 ≤ Real.exp (δ * B) := by
    calc
      _ = (4 * (B : ℝ)^11) * Real.exp ((δ / 4) * B) := by ring
      _ ≤ Real.exp ((3 * δ / 4) * B) * Real.exp ((δ / 4) * B) :=
        mul_le_mul_of_nonneg_right hsmall' (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (le_div_iff₀ (pow_pos hB0 10)).mpr
  exact ((mul_le_mul_of_nonneg_right hbound (pow_nonneg hB0.le 10)).trans htotal).trans hH

end JointDickman

end OAI
