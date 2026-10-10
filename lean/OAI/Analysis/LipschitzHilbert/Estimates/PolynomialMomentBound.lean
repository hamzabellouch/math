import OAI.Analysis.LipschitzHilbert.Estimates.TopWindowMoments

namespace OAI

/-! Put the explicit John--Nirenberg moment expression in the polynomial
form needed when the moment order grows with the manuscript parameter. -/

noncomputable section
open scoped ENNReal

namespace LipschitzHilbert

theorem polynomial_moment_majorant (Q R : ℝ) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (n : ℕ) (hn : 1 ≤ n) :
    (2:ℝ)^n * (7*((n:ℝ)*Q)^n+R^n) ≤ (16*(Q+R+1)*(n:ℝ))^n := by
  let S := Q+R+1
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hA : (n:ℝ)*Q ≤ (n:ℝ)*S := by dsimp [S]; nlinarith
  have hB : R ≤ (n:ℝ)*S := by
    have h := mul_le_mul_of_nonneg_right hnR hS
    dsimp [S] at h ⊢
    nlinarith
  have hAn := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg n) hQ) hA n
  have hBn := pow_le_pow_left₀ hR hB n
  have h8 : (8:ℝ) ≤ 8^n := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 8) hn
  calc
    _ ≤ 2^n * (8*((n:ℝ)*S)^n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ ≤ 2^n * (8^n*((n:ℝ)*S)^n) := by gcongr
    _ = (16*(Q+R+1)*(n:ℝ))^n := by
      rw [← mul_assoc, ← mul_pow, ← mul_pow]
      congr 1
      dsimp [S]
      ring

theorem ennreal_polynomial_moment_majorant (Q R : ℝ) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (n : ℕ) (hn : 1 ≤ n) :
    (2:ℝ≥0∞)^(n:ℝ) * (7*ENNReal.ofReal (((n:ℝ)*Q)^(n:ℝ)) +
      (ENNReal.ofReal R)^(n:ℝ)) ≤ ENNReal.ofReal ((16*(Q+R+1)*(n:ℝ))^n) := by
  have h := ENNReal.ofReal_le_ofReal (polynomial_moment_majorant Q R hQ hR n hn)
  simpa only [Real.rpow_natCast, ENNReal.rpow_natCast,
    ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2^n),
    ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ 7*((n:ℝ)*Q)^n) (pow_nonneg hR n),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 7),
    ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_pow hR,
    ENNReal.ofReal_ofNat] using h

def lineMomentBase (C D branching : ℝ) : ℝ :=
  16 * (((branching+2)*(2*Real.sqrt D+4*(C*(4*Real.pi)^2)))/Real.log (3/2) +
    Real.sqrt D + 1)

theorem lineMomentBase_pos (C D branching : ℝ) (hC : 0 ≤ C) (hb : 0 ≤ branching) :
    0 < lineMomentBase C D branching := by
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  unfold lineMomentBase
  positivity

theorem line_moment_expression_le (C D branching : ℝ) (hC : 0 ≤ C) (hb : 0 ≤ branching)
    (n : ℕ) (hn : 1 ≤ n) :
    (2:ℝ≥0∞)^(n:ℝ) * (7 * ENNReal.ofReal
      ((((n:ℝ)*((branching+2)*(2*Real.sqrt D+4*(C*(4*Real.pi)^2))))/Real.log (3/2))^(n:ℝ)) +
      (ENNReal.ofReal (Real.sqrt D))^(n:ℝ)) ≤
    ENNReal.ofReal ((lineMomentBase C D branching*(n:ℝ))^n) := by
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  have hQ : 0 ≤ ((branching+2)*(2*Real.sqrt D+4*(C*(4*Real.pi)^2)))/Real.log (3/2) := by
    positivity
  simpa only [lineMomentBase, mul_div_assoc] using
    ennreal_polynomial_moment_majorant _ _ hQ (Real.sqrt_nonneg D) n hn

end LipschitzHilbert

end

end OAI
