import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCircleTaylor

namespace OAI

/-! Fourier coefficient estimates for the small-circle character expansion. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

lemma cubicThetaCirclePhase_continuous (w : ℂ) (r : ℝ) :
    Continuous (cubicThetaCirclePhase w r) := by
  unfold cubicThetaCirclePhase cubicThetaCircleLinear
  exact (continuous_const.mul ((continuous_const.mul (fourier 1).continuous).add
    (continuous_const.mul (fourier (-1)).continuous))).cexp

lemma cubicThetaCirclePhase_norm (w : ℂ) (r : ℝ) (t : AddCircle (1:ℝ)) :
    ‖cubicThetaCirclePhase w r t‖=1 := by
  unfold cubicThetaCirclePhase
  rw [Complex.norm_exp,cubicThetaCircleLinear_real]
  simp [Complex.mul_re,Complex.mul_im]

lemma cubicThetaCirclePhase_integrable (w : ℂ) (r : ℝ) :
    Integrable (cubicThetaCirclePhase w r) AddCircle.haarAddCircle :=
  (cubicThetaCirclePhase_continuous w r).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma cubicThetaCircleTaylor_continuous (w : ℂ) (r : ℝ) (k : ℕ) :
    Continuous (cubicThetaCircleTaylor w r k) := by
  unfold cubicThetaCircleTaylor cubicThetaCirclePower
  exact continuous_finsetSum _ (fun j _ => continuous_const.mul
    (((continuous_const.mul (fourier 1).continuous).add
      (continuous_const.mul (fourier (-1)).continuous)).pow j))

theorem cubicThetaCirclePhase_coefficient_remainder (w : ℂ) (k : ℕ)
    {r : ℝ} (hr : 0≤r) :
    ‖fourierCoeff (cubicThetaCirclePhase w r) (k:ℤ)-
      ((2*Real.pi*Complex.I*(r:ℂ))^k/(k.factorial:ℂ))*w^k‖≤
        (4*Real.pi*‖w‖)^(k+1)*r^(k+1)/(k.factorial:ℝ) := by
  rw [←cubicThetaCircleTaylor_coefficient]
  exact cubicThetaCircle_coefficient_error (cubicThetaCirclePhase_integrable w r)
    ((cubicThetaCircleTaylor_continuous w r k).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (cubicThetaCirclePhase_remainder w k hr) (k:ℤ)

lemma cubicThetaCirclePhase_coefficient_norm (w : ℂ) (r : ℝ) (k : ℤ) :
    ‖fourierCoeff (cubicThetaCirclePhase w r) k‖≤1 := by
  unfold fourierCoeff
  have H := norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
    (f := fun t : AddCircle (1:ℝ) => fourier (-k) t • cubicThetaCirclePhase w r t)
    (C := 1) (ae_of_all _ (fun t => by
      simp only [norm_smul,fourier_apply,Circle.norm_coe,cubicThetaCirclePhase_norm,mul_one,le_refl]))
  simpa using H

end CubicFirstMoment

end

end OAI
