import OAI.NumberTheory.JointDickman.Amplification.RectangleRemainder

namespace OAI

/-! # Polynomial saving in the explicit rectangle remainder -/

namespace JointDickman

open Filter
open scoped Topology

theorem coefficient_rectangle_remainder_power {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ B : ℕ in atTop, ∀ L H : ℝ,
      Real.exp (δ * B) ≤ L → Real.exp (δ * B) ≤ H →
      coefficientScale B ^ 3 *
        (2 * (L + H + 2 * sieveCutoff (δ / 8) B) *
          (sieveCutoff (δ / 8) B + 1 : ℝ) * (sieveCutoff (δ / 8) B : ℝ) ^ 3) ≤ (L * H) / (B : ℝ) ^ 10 := by
  have hlim : Tendsto (fun B : ℕ => 16 * ((B : ℝ) ^ 13 /
      Real.exp ((δ / 2) * B))) atTop (𝓝 0) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 13 (by linarith : 0 < δ / 2)).tendsto_div_nhds_zero
    simpa only [Function.comp_def, mul_zero] using
      (h.comp tendsto_natCast_atTop_atTop).const_mul 16
  have hsmall := hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, coefficientScale_eventually_le,
    sieveCutoff_eventually (by linarith : 0 < δ / 8), eventually_gt_atTop 0]
    with B hsmallB hscale hcut hBpos
  intro L H hL hH
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hF : Real.exp ((δ / 8) * B) ≤ Real.exp (δ * B) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hz1 : (1 : ℝ) ≤ sieveCutoff (δ / 8) B := by exact_mod_cast (by omega : 1 ≤ sieveCutoff (δ / 8) B)
  have hbound := rectangle_remainder_bound (Real.exp_pos _) hL hH hz1 hcut.2.2.2 hF
  have heq : Real.exp ((δ / 8) * B) ^ 4 / Real.exp (δ * B) =
      (Real.exp ((δ / 2) * B))⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_neg]
    congr 1
    ring
  have hLH : 0 ≤ L * H := mul_nonneg ((Real.exp_pos _).le.trans hL)
    ((Real.exp_pos _).le.trans hH)
  have hL0 : 0 ≤ L := (Real.exp_pos _).le.trans hL
  have hH0 : 0 ≤ H := (Real.exp_pos _).le.trans hH
  calc
    _ ≤ (B : ℝ) ^ 3 * (16 * L * H * Real.exp ((δ / 8) * B) ^ 4 / Real.exp (δ * B)) :=
      mul_le_mul (pow_le_pow_left₀ (coefficientScale_nonneg B) hscale 3) hbound
        (by positivity) (pow_nonneg hB0 _)
    _ = (16 * ((B : ℝ) ^ 3 / Real.exp ((δ / 2) * B))) * (L * H) := by
      calc
        _ = 16 * (B : ℝ) ^ 3 * (Real.exp ((δ / 8) * B) ^ 4 / Real.exp (δ * B)) * (L * H) := by ring
        _ = _ := by rw [heq]; ring
    _ ≤ (1 / (B : ℝ) ^ 10) * (L * H) := by
      apply mul_le_mul_of_nonneg_right ?_ hLH
      have hBp : (0 : ℝ) < B := by exact_mod_cast hBpos
      apply (le_div_iff₀ (pow_pos hBp 10)).mpr
      convert hsmallB using 1; ring
    _ = _ := by ring

end JointDickman

end OAI
