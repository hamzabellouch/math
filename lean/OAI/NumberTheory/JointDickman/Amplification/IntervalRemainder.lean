import OAI.NumberTheory.JointDickman.Arithmetic.SieveScale

namespace OAI

/-! # Absorption of the two-root interval sieve remainder -/

namespace JointDickman

open Filter
open scoped Topology

theorem coefficient_interval_remainder_small {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ B : ℕ in atTop, ∀ L : ℝ, Real.exp (δ * B) ≤ L →
      coefficientScale B ^ 2 *
        (2 * (sieveCutoff (δ / 8) B + 1 : ℝ) * (sieveCutoff (δ / 8) B : ℝ) ^ 2) ≤ L := by
  have hlim : Tendsto (fun B : ℕ => 4 * ((B : ℝ) ^ 2 /
      Real.exp ((5 * δ / 8) * B))) atTop (𝓝 0) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 2 (by linarith : 0 < 5 * δ / 8)).tendsto_div_nhds_zero
    simpa only [Function.comp_def, mul_zero] using
      (h.comp tendsto_natCast_atTop_atTop).const_mul 4
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    coefficientScale_eventually_le, sieveCutoff_eventually (by linarith : 0 < δ / 8)]
    with B hsmall hscale hcut
  intro L hL
  have hF : 1 ≤ Real.exp ((δ / 8) * B) := by
    have hZ1 : (1 : ℝ) ≤ sieveCutoff (δ / 8) B := by exact_mod_cast (show 1 ≤ sieveCutoff (δ / 8) B by omega)
    exact hZ1.trans hcut.2.2.2
  have hZ0 : (0 : ℝ) ≤ sieveCutoff (δ / 8) B := Nat.cast_nonneg _
  have hZF : (sieveCutoff (δ / 8) B : ℝ) + 1 ≤ 2 * Real.exp ((δ / 8) * B) := by linarith [hcut.2.2.2]
  have heq : Real.exp ((δ / 8) * B) ^ 3 * Real.exp ((5 * δ / 8) * B) = Real.exp (δ * B) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (B : ℝ) ^ 2 * (2 * (2 * Real.exp ((δ / 8) * B)) * Real.exp ((δ / 8) * B) ^ 2) := by
      apply mul_le_mul (pow_le_pow_left₀ (coefficientScale_nonneg B) hscale 2)
      · gcongr
        exact hcut.2.2.2
      · positivity
      · positivity
    _ = (4 * ((B : ℝ) ^ 2 / Real.exp ((5 * δ / 8) * B))) * Real.exp (δ * B) := by
      rw [← heq]
      field_simp
      ring
    _ ≤ 1 * Real.exp (δ * B) := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
    _ ≤ L := by simpa only [one_mul] using hL

end JointDickman

end OAI
