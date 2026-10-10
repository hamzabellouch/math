import OAI.Combinatorics.Progressions.Estimates.NormalizedTupleParameterBounds

namespace OAI

section

namespace Erdos3

theorem spatialSamplingSize_of_exp_bounds {B W stride ρ ξ τ N : ℝ}
    (hB : 0 ≤ B) (hW : 0 ≤ W) (hs : 0 ≤ stride) (hρ : 0 ≤ ρ)
    (hξ : 0 < ξ) (hτ : 0 < τ)
    (hWB : W ≤ Real.exp B) (hsB : stride ≤ Real.exp B) (hρB : ρ ≤ Real.exp B)
    (hξB : ξ⁻¹ ≤ Real.exp B) (hτB : τ⁻¹ ≤ Real.exp B)
    (hN : Real.exp ((B + 10) ^ 2) ≤ N) :
    8 * (1 + W) * stride * ρ ≤ (ξ * τ) * N := by
  have hW1 := one_add_le_exp_succ hB hWB
  have hquot : (8 * (1 + W) * stride * ρ) / (ξ * τ) ≤ Real.exp (5 * B + 9) := by
    calc
      _ = 8 * (1 + W) * stride * ρ * ξ⁻¹ * τ⁻¹ := by
        rw [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ Real.exp 8 * Real.exp (B + 1) * Real.exp B * Real.exp B *
          Real.exp B * Real.exp B := by
        gcongr
        linarith [Real.add_one_le_exp (8 : ℝ)]
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hquotN := hquot.trans ((Real.exp_le_exp.mpr
    (show 5 * B + 9 ≤ (B + 10) ^ 2 by nlinarith [sq_nonneg B])).trans hN)
  simpa only [mul_comm N] using (div_le_iff₀ (mul_pos hξ hτ)).mp hquotN

theorem spatialSamplingSize_of_shiftedPower {B W stride ρ ξ τ N : ℝ} {a : ℕ}
    (ha : 10 ≤ a) (hB : 0 ≤ B) (hW : 0 ≤ W) (hs : 0 ≤ stride) (hρ : 0 ≤ ρ)
    (hξ : 0 < ξ) (hτ : 0 < τ)
    (hWB : W ≤ Real.exp B) (hsB : stride ≤ Real.exp B) (hρB : ρ ≤ Real.exp B)
    (hξB : ξ⁻¹ ≤ Real.exp B) (hτB : τ⁻¹ ≤ Real.exp B)
    (hN : Real.exp ((B + a) ^ a) ≤ N) :
    8 * (1 + W) * stride * ρ ≤ (ξ * τ) * N := by
  have ha' : (10 : ℝ) ≤ a := by exact_mod_cast ha
  have hpow : (B + 10) ^ 2 ≤ (B + a) ^ a :=
    (pow_le_pow_left₀ (by positivity) (by linarith) 2).trans
      (pow_le_pow_right₀ (by linarith) (by omega))
  exact spatialSamplingSize_of_exp_bounds hB hW hs hρ hξ hτ hWB hsB hρB hξB hτB
    ((Real.exp_le_exp.mpr hpow).trans hN)

end Erdos3

end

end OAI
