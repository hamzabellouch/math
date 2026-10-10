import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularContinuity

namespace OAI

/-! Exponential cusp decay survives every fixed angular frequency power. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaAngularAbsorption (k : ℕ) : ℝ := (k.factorial:ℝ)/(Real.pi/2)^k

lemma cubicThetaAngularAbsorption_pos (k : ℕ) : 0 < cubicThetaAngularAbsorption k := by
  unfold cubicThetaAngularAbsorption
  positivity

lemma cubicTheta_frequency_power_exp (k : ℕ) {r v : ℝ} (hr : 1/9 ≤ r) (hv : 1 ≤ v) :
    r^k*Real.exp (-Real.pi*r*v) ≤
      cubicThetaAngularAbsorption k*Real.exp (-(Real.pi/18)*v) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hf := pow_mul_exp_neg_le_factorial k (show 0 ≤ (Real.pi/2)*r by positivity)
  have hfac : r^k*Real.exp (-(Real.pi/2)*r) ≤ cubicThetaAngularAbsorption k := by
    apply (le_div_iff₀ (show 0 < (Real.pi/2)^k by positivity)).mpr
    calc
      _ = ((Real.pi/2)*r)^k*Real.exp (-((Real.pi/2)*r)) := by
        rw [show -(Real.pi/2)*r = -((Real.pi/2)*r) by ring,mul_pow]
        ring
      _ ≤ _ := hf
  have he1 : Real.exp (-(Real.pi/2)*r*v) ≤ Real.exp (-(Real.pi/2)*r) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonpos_left hv (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (le_of_lt (half_pos Real.pi_pos))) hr0.le)
    simpa only [mul_one] using h
  have he2 : Real.exp (-(Real.pi/2)*r*v) ≤ Real.exp (-(Real.pi/18)*v) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hr (show 0 ≤ Real.pi/2*v by positivity)
    convert neg_le_neg h using 1 <;> ring
  calc
    _ = (r^k*Real.exp (-(Real.pi/2)*r*v))*Real.exp (-(Real.pi/2)*r*v) := by
      conv_rhs => rw [mul_assoc,←Real.exp_add]
      congr 2
      ring
    _ ≤ (r^k*Real.exp (-(Real.pi/2)*r))*Real.exp (-(Real.pi/2)*r*v) := by
      gcongr
    _ ≤ cubicThetaAngularAbsorption k*Real.exp (-(Real.pi/18)*v) :=
      mul_le_mul hfac he2 (Real.exp_pos _).le (cubicThetaAngularAbsorption_pos k).le

lemma cubicThetaAngular_kernel_exp_bound (k : ℕ) {n : Eisenstein} (hn : n ≠ 0)
    {v : ℝ} (hv : 1 ≤ v) :
    ‖cubicThetaFrequency n‖^k*‖cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)‖ ≤
      (cubicWhittakerMixedConstant*cubicThetaAngularAbsorption k*81^(8/3:ℝ))*
        norm n^(-8/3:ℝ)*Real.exp (-(Real.pi/18)*v) := by
  have hr := cubicThetaFrequency_pos hn
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hD := cubicWhittakerMixedConstant_pos.le
  have hw := cubicThetaWhittaker_mixed_bound (mul_pos hr hv0)
  rw [Real.mul_rpow hr.le hv0.le] at hw
  have hb := cubicTheta_frequency_power_exp k (cubicThetaFrequency_lower hn) hv
  have hvp : v^(-16/3:ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hv (by norm_num)
  calc
    _ ≤ ‖cubicThetaFrequency n‖^k*(cubicWhittakerMixedConstant*
        (‖cubicThetaFrequency n‖^(-16/3:ℝ)*v^(-16/3:ℝ))*
          Real.exp (-Real.pi*(‖cubicThetaFrequency n‖*v))) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = (cubicWhittakerMixedConstant*‖cubicThetaFrequency n‖^(-16/3:ℝ))*v^(-16/3:ℝ)*
        (‖cubicThetaFrequency n‖^k*Real.exp (-Real.pi*‖cubicThetaFrequency n‖*v)) := by
      rw [show -Real.pi*(‖cubicThetaFrequency n‖*v) =
        -Real.pi*‖cubicThetaFrequency n‖*v by ring]
      ring
    _ ≤ (cubicWhittakerMixedConstant*‖cubicThetaFrequency n‖^(-16/3:ℝ))*1*
        (cubicThetaAngularAbsorption k*Real.exp (-(Real.pi/18)*v)) := by
      gcongr
    _ = _ := by
      rw [cubicThetaFrequency_rpow hn]
      norm_num only
      ring

def cubicThetaAngularExpConstant (C : ℝ) (ℓ : ℤ) : ℝ :=
  (C*cubicWhittakerMixedConstant*cubicThetaAngularAbsorption ℓ.natAbs*81^(8/3:ℝ))*
    ∑' n : Eisenstein, norm n^(-5/3:ℝ)

lemma cubicThetaAngular_term_exp_bound {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (ℓ : ℤ) (hv : 1 ≤ v) (z : ℂ) (n : Eisenstein) :
    ‖cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) z v n‖ ≤
      (C*cubicWhittakerMixedConstant*cubicThetaAngularAbsorption ℓ.natAbs*81^(8/3:ℝ)*
        Real.exp (-(Real.pi/18)*v))*norm n^(-5/3:ℝ) := by
  by_cases hn : n = 0
  · simp [cubicThetaSeriesTerm,hn,norm]
  · have hN := norm_pos_of_ne_zero hn
    simp only [cubicThetaSeriesTerm,hn,ite_false,norm_mul,Circle.norm_coe,mul_one,
      cubicThetaAngularCoefficient_norm ℓ hn]
    have hp : norm n*norm n^(-8/3:ℝ) = norm n^(-5/3:ℝ) := by
      calc
        _ = norm n^(1:ℝ)*norm n^(-8/3:ℝ) := by rw [Real.rpow_one]
        _ = norm n^(1+(-8/3:ℝ)) := (Real.rpow_add hN _ _).symm
        _ = _ := by congr 1; ring
    calc
      _ = ‖a n‖*(‖cubicThetaFrequency n‖^ℓ.natAbs*
          ‖cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)‖) := by ring
      _ ≤ (C*norm n)*((cubicWhittakerMixedConstant*cubicThetaAngularAbsorption ℓ.natAbs*81^(8/3:ℝ))*
          norm n^(-8/3:ℝ)*Real.exp (-(Real.pi/18)*v)) :=
        mul_le_mul (ha n hn) (cubicThetaAngular_kernel_exp_bound ℓ.natAbs hn hv)
          (mul_nonneg (by positivity) (_root_.norm_nonneg _)) (mul_nonneg hC hN.le)
      _ = _ := by
        calc
          _ = (C*cubicWhittakerMixedConstant*cubicThetaAngularAbsorption ℓ.natAbs*81^(8/3:ℝ)*
              Real.exp (-(Real.pi/18)*v))*(norm n*norm n^(-8/3:ℝ)) := by ring
          _ = _ := by rw [hp]

/-- Uniform exponential decrease of each fixed angular theta series. -/
theorem cubicThetaAngular_exponential_bound {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (ℓ : ℤ) (hv : 1 ≤ v) (z : ℂ) :
    ‖cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (z,v)‖ ≤
      cubicThetaAngularExpConstant C ℓ*Real.exp (-(Real.pi/18)*v) := by
  have hs := cubicThetaAngular_summable hC ha ℓ (zero_lt_one.trans_le hv) z
  have hm := (summable_eisenstein_norm_rpow (by norm_num : (1:ℝ) < 5/3)).mul_left
    (C*cubicWhittakerMixedConstant*cubicThetaAngularAbsorption ℓ.natAbs*81^(8/3:ℝ)*
      Real.exp (-(Real.pi/18)*v))
  calc
    _ ≤ ∑' n : Eisenstein, ‖cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) z v n‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : Eisenstein, (C*cubicWhittakerMixedConstant*cubicThetaAngularAbsorption ℓ.natAbs*81^(8/3:ℝ)*
        Real.exp (-(Real.pi/18)*v))*norm n^(-5/3:ℝ) :=
      Summable.tsum_le_tsum (cubicThetaAngular_term_exp_bound hC ha ℓ hv z) hs.norm (by
        simpa only [neg_div] using hm)
    _ = _ := by rw [tsum_mul_left]; unfold cubicThetaAngularExpConstant; ring

end CubicFirstMoment

end

end OAI
