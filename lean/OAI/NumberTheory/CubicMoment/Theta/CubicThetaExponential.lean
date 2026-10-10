import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeightDecay
import OAI.NumberTheory.CubicMoment.Estimates.CubicWhittakerExponential

namespace OAI

/-! Uniform exponential decay of the nonconstant cubic cusp expansion. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_lower {n : Eisenstein} (hn : n ≠ 0) :
    (1/9:ℝ) ≤ ‖cubicThetaFrequency n‖ := by
  have hN := one_le_norm hn
  have hsq := cubicThetaFrequency_sq n
  have hp := (cubicThetaFrequency_pos hn).le
  nlinarith

lemma cubicThetaWhittaker_frequency_exp_bound {n : Eisenstein} (hn : n ≠ 0)
    {v : ℝ} (hv : 1 ≤ v) :
    ‖cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)‖ ≤
      (cubicWhittakerMixedConstant*81^(8/3:ℝ))*norm n^(-8/3:ℝ)*
        Real.exp (-(Real.pi/9)*v) := by
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hp := cubicThetaFrequency_pos hn
  have hw := cubicThetaWhittaker_mixed_bound (mul_pos hp hv0)
  rw [Real.mul_rpow hp.le hv0.le,cubicThetaFrequency_rpow hn] at hw
  have h1 : -(-16/3:ℝ)/2 = 8/3 := by norm_num
  have h2 : (-16/3:ℝ)/2 = -8/3 := by norm_num
  rw [h1,h2] at hw
  have hvp : v^(-16/3:ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hv (by norm_num)
  have he : Real.exp (-Real.pi*(‖cubicThetaFrequency n‖*v)) ≤
      Real.exp (-(Real.pi/9)*v) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (cubicThetaFrequency_lower hn) hv0.le
    nlinarith [Real.pi_pos]
  apply hw.trans
  have hD := cubicWhittakerMixedConstant_pos.le
  have hnp := Real.rpow_nonneg (norm_nonneg n) (-8/3:ℝ)
  calc
    _ ≤ cubicWhittakerMixedConstant*(81^(8/3:ℝ)*norm n^(-8/3:ℝ)*1)*
        Real.exp (-(Real.pi/9)*v) := by gcongr
    _ = _ := by ring

lemma cubicThetaSeriesTerm_exp_bound {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (hv : 1 ≤ v) (z : ℂ) (n : Eisenstein) :
    ‖cubicThetaSeriesTerm a z v n‖ ≤
      (C*cubicWhittakerMixedConstant*81^(8/3:ℝ))*Real.exp (-(Real.pi/9)*v)*
        norm n^(-5/3:ℝ) := by
  have hD := cubicWhittakerMixedConstant_pos.le
  by_cases hn : n = 0
  · simp only [cubicThetaSeriesTerm,hn,ite_true,norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hD) (by positivity))
      (by positivity)) (Real.rpow_nonneg (norm_nonneg _) _)
  · simp only [cubicThetaSeriesTerm,hn,ite_false,norm_mul,Circle.norm_coe,mul_one]
    have hN := norm_pos_of_ne_zero hn
    calc
      _ ≤ (C*norm n)*((cubicWhittakerMixedConstant*81^(8/3:ℝ))*norm n^(-8/3:ℝ)*
          Real.exp (-(Real.pi/9)*v)) := mul_le_mul (ha n hn)
        (cubicThetaWhittaker_frequency_exp_bound hn hv) (_root_.norm_nonneg _) (mul_nonneg hC hN.le)
      _ = _ := by
        have he : norm n*norm n^(-8/3:ℝ) = norm n^(-5/3:ℝ) := by
          calc
            _ = norm n^(1:ℝ)*norm n^(-8/3:ℝ) := by rw [Real.rpow_one]
            _ = norm n^(1+(-8/3:ℝ)) := (Real.rpow_add hN _ _).symm
            _ = _ := by congr 1; ring
        calc
          _ = ((C*cubicWhittakerMixedConstant*81^(8/3:ℝ))*Real.exp (-(Real.pi/9)*v))*
              (norm n*norm n^(-8/3:ℝ)) := by ring
          _ = _ := by rw [he]

def cubicThetaExpConstant (C : ℝ) : ℝ :=
  (C*cubicWhittakerMixedConstant*81^(8/3:ℝ))*(∑' n : Eisenstein, norm n^(-5/3:ℝ))

/-- An explicit exponential bound uniform in horizontal position. -/
theorem cubicThetaNonconstant_exponential_bound {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (hv : 1 ≤ v) (z : ℂ) :
    ‖cubicThetaNonconstant a (z,v)‖ ≤ cubicThetaExpConstant C*Real.exp (-(Real.pi/9)*v) := by
  have hs := cubicThetaSeries_summable hC ha (zero_lt_one.trans_le hv) z
  let D := (C*cubicWhittakerMixedConstant*81^(8/3:ℝ))*Real.exp (-(Real.pi/9)*v)
  have hmajor : Summable (fun n : Eisenstein => D*norm n^(-5/3:ℝ)) := by
    simpa only [neg_div] using
      (summable_eisenstein_norm_rpow (by norm_num : (1:ℝ) < 5/3)).mul_left D
  calc
    _ ≤ ∑' n : Eisenstein, ‖cubicThetaSeriesTerm a z v n‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : Eisenstein, D*norm n^(-5/3:ℝ) :=
      Summable.tsum_le_tsum (cubicThetaSeriesTerm_exp_bound hC ha hv z) hs.norm hmajor
    _ = _ := by rw [tsum_mul_left]; dsimp [D,cubicThetaExpConstant]; ring

end CubicFirstMoment

end

end OAI
