import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularFrequency
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalSeriesDerivative

namespace OAI

/-! Actual normalized Wirtinger derivatives of the theta expansion.
The two signs give the positive and negative angular Fourier towers. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaWirtingerPositive (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (deriv (fun t : ℝ => f (z+(t:ℂ))) 0-
    Complex.I*deriv (fun t : ℝ => f (z+(t:ℂ)*Complex.I)) 0)/(4*Real.pi*Complex.I)

def cubicThetaWirtingerNegative (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (deriv (fun t : ℝ => f (z+(t:ℂ))) 0+
    Complex.I*deriv (fun t : ℝ => f (z+(t:ℂ)*Complex.I)) 0)/(4*Real.pi*Complex.I)

lemma cubicTheta_tracePair_positive (w : ℂ) :
    (tracePair w 1:ℂ)-Complex.I*(tracePair w Complex.I:ℂ)=2*w := by
  apply Complex.ext <;> simp [tracePair]

lemma cubicTheta_tracePair_negative (w : ℂ) :
    (tracePair w 1:ℂ)+Complex.I*(tracePair w Complex.I:ℂ)=2*star w := by
  apply Complex.ext <;> simp [tracePair]

lemma cubicThetaAngular_horizontal_summable {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (hv : 0<v) (h z : ℂ) :
    Summable (fun n : Eisenstein => (2*Real.pi*Complex.I*(tracePair (cubicThetaFrequency n) h:ℂ))*
      cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) z v n) := by
  apply ((summable_eisenstein_norm_rpow (by norm_num : (1:ℝ)<4/3)).mul_left
    ((4*Real.pi*‖h‖)*(C*cubicWhittakerPowerConstant (ℓ.natAbs+1+3)*
      (9:ℝ)^(ℓ.natAbs+1)*81^(7/3:ℝ)*v^(4/3-2*(((ℓ.natAbs+1:ℕ):ℝ)+3))))).of_norm_bounded
  intro n
  simpa only [neg_div] using cubicThetaAngular_horizontal_term_bound hC ha ℓ hv h z n

lemma cubicThetaAngular_positive_term (a : Eisenstein → ℂ) (k : ℕ)
    (z : ℂ) (v : ℝ) (n : Eisenstein) :
    (2*Real.pi*Complex.I*(tracePair (cubicThetaFrequency n) 1:ℂ))*
        cubicThetaSeriesTerm (cubicThetaAngularCoefficient a (k:ℤ)) z v n-
      Complex.I*((2*Real.pi*Complex.I*(tracePair (cubicThetaFrequency n) Complex.I:ℂ))*
        cubicThetaSeriesTerm (cubicThetaAngularCoefficient a (k:ℤ)) z v n)=
    (4*Real.pi*Complex.I)*
      cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ((k+1:ℕ):ℤ)) z v n := by
  by_cases hn : n=0
  · simp only [cubicThetaSeriesTerm,hn,ite_true,mul_zero,sub_self]
  simp only [cubicThetaSeriesTerm,hn,ite_false,cubicThetaAngularCoefficient_nat_succ]
  have h := cubicTheta_tracePair_positive (cubicThetaFrequency n)
  linear_combination (2*Real.pi*Complex.I*cubicThetaAngularCoefficient a (k:ℤ) n*
    cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)*
      (Real.fourierChar (tracePair (cubicThetaFrequency n) z):ℂ))*h

lemma cubicThetaAngular_negative_term (a : Eisenstein → ℂ) (k : ℕ)
    (z : ℂ) (v : ℝ) (n : Eisenstein) :
    (2*Real.pi*Complex.I*(tracePair (cubicThetaFrequency n) 1:ℂ))*
        cubicThetaSeriesTerm (cubicThetaAngularCoefficient a (-(k:ℤ))) z v n+
      Complex.I*((2*Real.pi*Complex.I*(tracePair (cubicThetaFrequency n) Complex.I:ℂ))*
        cubicThetaSeriesTerm (cubicThetaAngularCoefficient a (-(k:ℤ))) z v n)=
    (4*Real.pi*Complex.I)*
      cubicThetaSeriesTerm (cubicThetaAngularCoefficient a (-((k+1:ℕ):ℤ))) z v n := by
  by_cases hn : n=0
  · simp only [cubicThetaSeriesTerm,hn,ite_true,mul_zero,add_zero]
  simp only [cubicThetaSeriesTerm,hn,ite_false,cubicThetaAngularCoefficient_neg_nat_succ]
  have h := cubicTheta_tracePair_negative (cubicThetaFrequency n)
  linear_combination (2*Real.pi*Complex.I*cubicThetaAngularCoefficient a (-(k:ℤ)) n*
    cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)*
      (Real.fourierChar (tracePair (cubicThetaFrequency n) z):ℂ))*h

theorem cubicThetaWirtingerPositive_angular {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (k : ℕ) (hv : 0<v) (z : ℂ) :
    cubicThetaWirtingerPositive
      (fun z => cubicThetaNonconstant (cubicThetaAngularCoefficient a (k:ℤ)) (z,v)) z=
      cubicThetaNonconstant (cubicThetaAngularCoefficient a ((k+1:ℕ):ℤ)) (z,v) := by
  have hx := cubicThetaAngular_horizontal_summable hC ha (k:ℤ) hv 1 z
  have hy := (cubicThetaAngular_horizontal_summable hC ha (k:ℤ) hv Complex.I z).mul_left Complex.I
  unfold cubicThetaWirtingerPositive
  have dx := cubicThetaAngular_horizontal_deriv hC ha (k:ℤ) hv 1 z 0
  simp only [mul_one,Complex.ofReal_zero,add_zero] at dx
  rw [dx,cubicThetaAngular_horizontal_deriv hC ha (k:ℤ) hv Complex.I z 0]
  simp only [Complex.ofReal_zero,zero_mul,add_zero]
  rw [←tsum_mul_left,←hx.tsum_sub hy]
  simp_rw [cubicThetaAngular_positive_term]
  rw [tsum_mul_left]
  change (4*Real.pi*Complex.I)*_/(4*Real.pi*Complex.I)=_
  exact mul_div_cancel_left₀ _ (by exact mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)

theorem cubicThetaWirtingerNegative_angular {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (k : ℕ) (hv : 0<v) (z : ℂ) :
    cubicThetaWirtingerNegative
      (fun z => cubicThetaNonconstant (cubicThetaAngularCoefficient a (-(k:ℤ))) (z,v)) z=
      cubicThetaNonconstant (cubicThetaAngularCoefficient a (-((k+1:ℕ):ℤ))) (z,v) := by
  have hx := cubicThetaAngular_horizontal_summable hC ha (-(k:ℤ)) hv 1 z
  have hy := (cubicThetaAngular_horizontal_summable hC ha (-(k:ℤ)) hv Complex.I z).mul_left Complex.I
  unfold cubicThetaWirtingerNegative
  have dx := cubicThetaAngular_horizontal_deriv hC ha (-(k:ℤ)) hv 1 z 0
  simp only [mul_one,Complex.ofReal_zero,add_zero] at dx
  rw [dx,cubicThetaAngular_horizontal_deriv hC ha (-(k:ℤ)) hv Complex.I z 0]
  simp only [Complex.ofReal_zero,zero_mul,add_zero]
  rw [←tsum_mul_left,←hx.tsum_add hy]
  simp_rw [cubicThetaAngular_negative_term]
  rw [tsum_mul_left]
  change (4*Real.pi*Complex.I)*_/(4*Real.pi*Complex.I)=_
  exact mul_div_cancel_left₀ _ (by exact mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)

end CubicFirstMoment

end

end OAI
