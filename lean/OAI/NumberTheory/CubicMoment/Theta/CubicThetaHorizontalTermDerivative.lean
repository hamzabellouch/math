import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularContinuity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierMode
import Mathlib.Analysis.Calculus.SmoothSeries

namespace OAI

/-! Actual horizontal derivatives of the fixed-angular Fourier terms,
with the summable majorant needed to differentiate their series. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_tracePair_abs (w h : ℂ) : |tracePair w h|≤2*‖w‖*‖h‖ := by
  unfold tracePair
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have he := mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm (w*h)) (by norm_num : (0:ℝ)≤2)
  simpa only [norm_mul,mul_comm,mul_left_comm,mul_assoc] using he

theorem cubicThetaSeriesTerm_horizontal_hasDerivAt (a : Eisenstein → ℂ)
    (h z : ℂ) (v : ℝ) (n : Eisenstein) (t : ℝ) :
    HasDerivAt (fun u : ℝ => cubicThetaSeriesTerm a (z+(u:ℂ)*h) v n)
      ((2*Real.pi*Complex.I*(tracePair (cubicThetaFrequency n) h:ℂ))*
        cubicThetaSeriesTerm a (z+(t:ℂ)*h) v n) t := by
  classical
  by_cases hn : n=0
  · simp only [cubicThetaSeriesTerm,hn,ite_true,mul_zero]
    exact hasDerivAt_const t 0
  let α := tracePair (cubicThetaFrequency n) h
  let β := tracePair (cubicThetaFrequency n) z
  have hphase (u : ℝ) : tracePair (cubicThetaFrequency n) (z+(u:ℂ)*h)=α*u+β := by
    dsimp [α,β,tracePair]
    simp only [mul_add,Complex.add_re,mul_assoc,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    ring
  have he : (fun u : ℝ => cubicThetaSeriesTerm a (z+(u:ℂ)*h) v n)=
      fun u => (a n*cubicThetaWhittaker (‖cubicThetaFrequency n‖*v))*
        (Real.fourierChar (α*u+β):ℂ) := by
    funext u
    simp only [cubicThetaSeriesTerm,hn,ite_false,hphase]
  rw [he]
  have hd := (cubicTheta_affineCharacter_hasDerivAt α β t).const_mul
    (a n*cubicThetaWhittaker (‖cubicThetaFrequency n‖*v))
  convert hd using 1
  simp only [cubicThetaSeriesTerm,hn,ite_false,hphase]
  dsimp [α]
  ring

lemma cubicThetaAngular_term_next_norm (a : Eisenstein → ℂ) (ℓ : ℤ)
    (z : ℂ) (v : ℝ) (n : Eisenstein) :
    ‖cubicThetaFrequency n‖*‖cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) z v n‖=
      ‖cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ((ℓ.natAbs+1:ℕ):ℤ)) z v n‖ := by
  classical
  by_cases hn : n=0
  · simp only [cubicThetaSeriesTerm,hn,ite_true,norm_zero,mul_zero]
  · simp only [cubicThetaSeriesTerm,hn,ite_false,norm_mul,Circle.norm_coe,mul_one,
      cubicThetaAngularCoefficient_norm _ hn,Int.natAbs_natCast,pow_succ]
    ring

lemma cubicThetaAngular_horizontal_term_bound {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (hv : 0<v) (h z : ℂ) (n : Eisenstein) :
    ‖(2*Real.pi*Complex.I*(tracePair (cubicThetaFrequency n) h:ℂ))*
        cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) z v n‖≤
      (4*Real.pi*‖h‖)*(C*cubicWhittakerPowerConstant (ℓ.natAbs+1+3)*
        (9:ℝ)^(ℓ.natAbs+1)*81^(7/3:ℝ)*v^(4/3-2*(((ℓ.natAbs+1:ℕ):ℝ)+3)))*
          norm n^(-4/3:ℝ) := by
  have ht := cubicTheta_tracePair_abs (cubicThetaFrequency n) h
  have hb := cubicThetaAngular_term_bound hC ha ((ℓ.natAbs+1:ℕ):ℤ) hv z n
  simp only [Int.natAbs_natCast] at hb
  calc
    _ = (2*Real.pi)*|tracePair (cubicThetaFrequency n) h| *
        ‖cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) z v n‖ := by
      simp only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      norm_num
    _ ≤ (2*Real.pi)*(2*‖cubicThetaFrequency n‖*‖h‖)*
        ‖cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) z v n‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by positivity)) (_root_.norm_nonneg _)
    _ = (4*Real.pi*‖h‖)*
        ‖cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ((ℓ.natAbs+1:ℕ):ℤ)) z v n‖ := by
      rw [←cubicThetaAngular_term_next_norm]
      ring
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left hb (by positivity : 0≤4*Real.pi*‖h‖) using 1
      ring

end CubicFirstMoment

end

end OAI
