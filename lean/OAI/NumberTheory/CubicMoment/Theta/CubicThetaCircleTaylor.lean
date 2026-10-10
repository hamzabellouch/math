import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCirclePolynomial
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaImaginaryTaylor

namespace OAI

/-! Uniform angular Taylor extraction for one Fourier character. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

def cubicThetaCircleLinear (w : ℂ) (t : AddCircle (1:ℝ)) : ℂ :=
  w*fourier 1 t+star w*fourier (-1) t

def cubicThetaCirclePhase (w : ℂ) (r : ℝ) (t : AddCircle (1:ℝ)) : ℂ :=
  Complex.exp ((2*Real.pi*Complex.I*(r:ℂ))*cubicThetaCircleLinear w t)

def cubicThetaCircleTaylor (w : ℂ) (r : ℝ) (k : ℕ) (t : AddCircle (1:ℝ)) : ℂ :=
  ∑ j∈Finset.range (k+1),
    ((2*Real.pi*Complex.I*(r:ℂ))^j/(j.factorial:ℂ))*cubicThetaCirclePower w j t

lemma cubicThetaCircleLinear_real (w : ℂ) (t : AddCircle (1:ℝ)) :
    cubicThetaCircleLinear w t= (2*(w*fourier 1 t).re:ℝ) := by
  unfold cubicThetaCircleLinear
  rw [fourier_neg]
  simpa only [map_mul,Complex.star_def] using Complex.add_conj (w*fourier 1 t)

lemma cubicThetaCircleLinear_norm (w : ℂ) (t : AddCircle (1:ℝ)) :
    ‖cubicThetaCircleLinear w t‖≤2*‖w‖ := by
  calc
    _ ≤ ‖w*fourier 1 t‖+‖star w*fourier (-1) t‖ := norm_add_le _ _
    _ = _ := by simp only [norm_mul,fourier_apply,Circle.norm_coe,norm_star,mul_one]; ring

lemma cubicThetaCircleTaylor_coefficient (w : ℂ) (r : ℝ) (k : ℕ) :
    fourierCoeff (cubicThetaCircleTaylor w r k) (k:ℤ)=
      ((2*Real.pi*Complex.I*(r:ℂ))^k/(k.factorial:ℂ))*w^k := by
  classical
  have hi (j : ℕ) (_ : j∈Finset.range (k+1)) : Integrable
      (fun t : AddCircle (1:ℝ) => ((2*Real.pi*Complex.I*(r:ℂ))^j/(j.factorial:ℂ))*
        cubicThetaCirclePower w j t) AddCircle.haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact continuous_const.mul (((continuous_const.mul (fourier 1).continuous).add
      (continuous_const.mul (fourier (-1)).continuous)).pow j)
  have he : cubicThetaCircleTaylor w r k=
      ∑ j∈Finset.range (k+1),fun t : AddCircle (1:ℝ) =>
        ((2*Real.pi*Complex.I*(r:ℂ))^j/(j.factorial:ℂ))*cubicThetaCirclePower w j t := by
    funext t
    simp only [cubicThetaCircleTaylor,Finset.sum_apply]
  rw [he,fourierCoeff.sum _ _ hi]
  simp only [Finset.sum_apply,fourierCoeff.const_mul]
  rw [Finset.sum_eq_single k]
  · rw [cubicThetaCirclePower_coefficient_top]
  · intro j hj hjk
    rw [cubicThetaCirclePower_coefficient_above w (by have := Finset.mem_range.mp hj; omega),mul_zero]
  · simp

theorem cubicThetaCirclePhase_remainder (w : ℂ) (k : ℕ) {r : ℝ} (hr : 0≤r)
    (t : AddCircle (1:ℝ)) :
    ‖cubicThetaCirclePhase w r t-cubicThetaCircleTaylor w r k t‖≤
      (4*Real.pi*‖w‖)^(k+1)*r^(k+1)/(k.factorial:ℝ) := by
  let c := (2*Real.pi*Complex.I)*cubicThetaCircleLinear w t
  have hc : c.re=0 := by
    dsimp [c]
    rw [cubicThetaCircleLinear_real]
    simp [Complex.mul_re,Complex.mul_im]
  have hn : ‖c‖≤4*Real.pi*‖w‖ := by
    calc
      _ = (2*Real.pi)*‖cubicThetaCircleLinear w t‖ := by
        dsimp [c]
        simp only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg Real.pi_pos.le,Complex.norm_ofNat]
      _ ≤ (2*Real.pi)*(2*‖w‖) :=
        mul_le_mul_of_nonneg_left (cubicThetaCircleLinear_norm w t) (by positivity)
      _ = _ := by ring
  have he : ∑ j∈Finset.range (k+1), (c*(r:ℂ))^j/(j.factorial:ℂ)=
      cubicThetaCircleTaylor w r k t := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [c,cubicThetaCirclePower,cubicThetaCircleLinear]
    rw [mul_pow,mul_pow,mul_pow]
    ring
  have H := cubicTheta_exp_imaginary_taylor c hc k hr
  rw [he] at H
  change ‖Complex.exp (c*(r:ℂ))-cubicThetaCircleTaylor w r k t‖≤_ at H
  have hphase : Complex.exp (c*(r:ℂ))=cubicThetaCirclePhase w r t := by
    unfold cubicThetaCirclePhase c
    congr 1
    ring
  rw [hphase] at H
  exact H.trans (by gcongr)

lemma cubicThetaCircle_coefficient_error {f g : AddCircle (1:ℝ)→ℂ}
    (hf : Integrable f AddCircle.haarAddCircle)
    (hg : Integrable g AddCircle.haarAddCircle) {B : ℝ}
    (hB : ∀ t, ‖f t-g t‖≤B) (k : ℤ) :
    ‖fourierCoeff f k-fourierCoeff g k‖≤B := by
  rw [fourierCoeff,fourierCoeff,←integral_sub (hf.fourier_smul _) (hg.fourier_smul _)]
  have H := norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
    (f := fun t : AddCircle (1:ℝ) => fourier (-k) t • f t-fourier (-k) t • g t)
    (ae_of_all _ (fun t => by
      rw [←smul_sub,norm_smul,fourier_apply,Circle.norm_coe,one_mul]
      exact hB t))
  simpa using H

end CubicFirstMoment

end

end OAI
