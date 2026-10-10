import OAI.Combinatorics.EditApproximation.Refinement.StageWarmup
import OAI.Combinatorics.EditApproximation.Geometry.GroupSmallConstants

namespace OAI

/-! Computed parameters for the actual local energy and online inequalities. -/

namespace EditApproximation

theorem refinementFactor_le {A : ℚ} {F : ℕ} (hA : 1 ≤ A) (hF : 1 ≤ F) :
    refinementFactor A F ≤ A := by
  apply max_le hA
  have hFQ : (1 : ℚ) ≤ F := by exact_mod_cast hF
  apply (div_le_iff₀ (by linarith only [hFQ] : (0 : ℚ) < F)).2
  have h := mul_le_mul_of_nonneg_left hFQ (by linarith only [hA] : 0 ≤ A)
  simpa only [mul_one] using h

theorem computed_initialFactor_twice_le_P (N : ℕ) (hN : 0 < N) :
    2 * (integerParameters N).initialFactor ≤ (integerParameters N).P := by
  let H := inputHeight N
  let p := coarseExponent (inputSmallLog N)
  have hH : 2 ≤ H := by
    have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (heightExponent_pos N hN)
    simpa only [H, inputHeight, pow_one] using h
  have hHone : 1 ≤ H := by omega
  have hpow : 2 ≤ H ^ 16 := hH.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hHone (by decide : 1 ≤ 16))
  change 2 * H ^ (p + 4) ≤ H ^ (p + 20)
  calc
    2 * H ^ (p + 4) ≤ H ^ (p + 4) * H ^ 16 := by
      simpa only [mul_comm] using Nat.mul_le_mul_left (H ^ (p + 4)) hpow
    _ = H ^ (p + 20) := by
      rw [← pow_add]

theorem computed_refinementFactor_spacing (N : ℕ) (hN : 0 < N) (A : ℚ)
    (hA : 1 ≤ A) (hupper : A ≤ (integerParameters N).initialFactor) :
    2 * (refinementFactor A (inputSmallLog N) : ℝ) ≤ (integerParameters N).P := by
  have hfactor := refinementFactor_le hA (show 1 ≤ inputSmallLog N from Nat.one_le_two_pow)
  have hnum : (2 : ℚ) * (integerParameters N).initialFactor ≤ (integerParameters N).P := by
    exact_mod_cast computed_initialFactor_twice_le_P N hN
  have hQ : (2 : ℚ) * refinementFactor A (inputSmallLog N) ≤ (integerParameters N).P := by
    linarith only [hfactor, hupper, hnum]
  exact_mod_cast hQ

theorem computed_online_range (ell : ℕ) (hell : 8 ≤ ell) :
    0 < (rationalParameters ell).eta ∧ 0 ≤ (rationalParameters ell).kappa ∧
      (rationalParameters ell).kappa ≤ 1 / 2 ∧
      ((rationalParameters ell).eta : ℝ) *
        (2 * ((rationalParameters ell).delta : ℝ) +
          8 * (128 * (ell : ℝ)) * ((rationalParameters ell).theta : ℝ)) ≤
        ((rationalParameters ell).kappa : ℝ) := by
  have hellQ : (8 : ℚ) ≤ ell := by exact_mod_cast hell
  have he0 : (0 : ℚ) < ell := by linarith only [hellQ]
  have hpow : (2 : ℚ) ≤ (ell : ℚ) ^ 4 := by
    exact (by linarith only [hellQ] : (2 : ℚ) ≤ ell).trans (by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith only [hellQ] : (1 : ℚ) ≤ ell)
        (by decide : 1 ≤ 4))
  have hhalf : (1 : ℚ) / (ell : ℚ) ^ 4 ≤ 1 / 2 := by
    exact (div_le_div_iff₀ (pow_pos he0 4) (by norm_num : (0 : ℚ) < 2)).2 (by simpa using hpow)
  have hrange := group_online_range_small hellQ
  have heta := group_online_eta_range (by linarith only [hellQ] : (3 : ℚ) ≤ ell)
  have h := mul_le_mul_of_nonneg_left hrange (pow_nonneg he0.le 5)
  have hQ : (ell : ℚ) ^ 5 * (2 * (1 / (ell : ℚ) ^ 10) +
      8 * (128 * ell) * (1 / (ell : ℚ) ^ 40)) ≤ 1 / (ell : ℚ) ^ 4 := by
    linarith only [h, heta]
  refine ⟨pow_pos he0 5, (by positivity : (0 : ℚ) ≤ 1 / (ell : ℚ) ^ 4), hhalf, ?_⟩
  have hR := (Rat.cast_le (K := ℝ)).mpr hQ
  simpa only [rationalParameters, Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_pow,
    Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, Nat.cast_mul, Nat.cast_ofNat] using hR

end EditApproximation

end OAI
