import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCircleExtraction
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Small-circle coefficient extraction for an absolutely convergent Fourier series.
Only the zeroth, selected and next absolute frequency moments are used. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩
variable {ι : Type*}

def cubicThetaCircleSeries (a w : ι→ℂ) (r : ℝ) (t : AddCircle (1:ℝ)) : ℂ :=
  ∑' n, a n*cubicThetaCirclePhase (w n) r t

lemma cubicThetaCircleSeries_continuous {a w : ι→ℂ}
    (ha : Summable (fun n => ‖a n‖)) (r : ℝ) :
    Continuous (cubicThetaCircleSeries a w r) := by
  exact continuous_tsum
    (fun n => continuous_const.mul (cubicThetaCirclePhase_continuous (w n) r)) ha
    (fun n t => by simp only [norm_mul,cubicThetaCirclePhase_norm,mul_one,le_refl])

variable [Countable ι]

lemma cubicThetaCircleSeries_coefficient {a w : ι→ℂ}
    (ha : Summable (fun n => ‖a n‖)) (r : ℝ) (k : ℤ) :
    fourierCoeff (cubicThetaCircleSeries a w r) k=
      ∑' n, a n*fourierCoeff (cubicThetaCirclePhase (w n) r) k := by
  let f := fun n t => a n*(fourier (-k) t*cubicThetaCirclePhase (w n) r t)
  have hi (n : ι) : Integrable (f n) AddCircle.haarAddCircle :=
    ((cubicThetaCirclePhase_integrable (w n) r).fourier_smul (-k)).const_mul (a n)
  have hn (n : ι) : (∫ t, ‖f n t‖ ∂AddCircle.haarAddCircle)=‖a n‖ := by
    simp only [f,norm_mul,fourier_apply,Circle.norm_coe,cubicThetaCirclePhase_norm,mul_one]
    simp
  have hs : Summable (fun n => ∫ t, ‖f n t‖ ∂AddCircle.haarAddCircle) := by
    simpa only [hn] using ha
  calc
    _ = ∫ t, ∑' n, f n t ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with t
      change fourier (-k) t*(∑' n, a n*cubicThetaCirclePhase (w n) r t)=
        ∑' n, a n*(fourier (-k) t*cubicThetaCirclePhase (w n) r t)
      rw [←tsum_mul_left]
      apply tsum_congr
      intro n
      ring
    _ = ∑' n, ∫ t, f n t ∂AddCircle.haarAddCircle :=
      (integral_tsum_of_summable_integral_norm hi hs).symm
    _ = _ := by
      apply tsum_congr
      intro n
      exact integral_const_mul _ _

theorem cubicThetaCircleSeries_remainder {a w : ι→ℂ}
    (ha : Summable (fun n => ‖a n‖)) (k : ℕ)
    (hk : Summable (fun n => a n*w n^k))
    (hk1 : Summable (fun n => ‖a n‖*‖w n‖^(k+1))) {r : ℝ} (hr : 0≤r) :
    ‖fourierCoeff (cubicThetaCircleSeries a w r) (k:ℤ)-
      ((2*Real.pi*Complex.I*(r:ℂ))^k/(k.factorial:ℂ))*(∑' n, a n*w n^k)‖≤
        ((4*Real.pi)^(k+1)*r^(k+1)/(k.factorial:ℝ))*
          (∑' n, ‖a n‖*‖w n‖^(k+1)) := by
  let D : ℂ := (2*Real.pi*Complex.I*(r:ℂ))^k/(k.factorial:ℂ)
  let K : ℝ := (4*Real.pi)^(k+1)*r^(k+1)/(k.factorial:ℝ)
  have hK : 0≤K := by dsimp [K]; positivity
  have hsF : Summable (fun n => a n*fourierCoeff (cubicThetaCirclePhase (w n) r) (k:ℤ)) :=
    ha.of_norm_bounded (fun n => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (cubicThetaCirclePhase_coefficient_norm (w n) r (k:ℤ))
        (norm_nonneg _)).trans_eq (mul_one _))
  have hsM : Summable (fun n => D*(a n*w n^k)) := hk.mul_left D
  have hB (n : ι) :
      ‖a n*fourierCoeff (cubicThetaCirclePhase (w n) r) (k:ℤ)-D*(a n*w n^k)‖≤
        K*(‖a n‖*‖w n‖^(k+1)) := by
    calc
      _ = ‖a n‖*‖fourierCoeff (cubicThetaCirclePhase (w n) r) (k:ℤ)-D*w n^k‖ := by
        rw [←norm_mul]
        congr 1
        ring
      _ ≤ ‖a n‖*((4*Real.pi*‖w n‖)^(k+1)*r^(k+1)/(k.factorial:ℝ)) :=
        mul_le_mul_of_nonneg_left (cubicThetaCirclePhase_coefficient_remainder (w n) k hr)
          (norm_nonneg _)
      _ = _ := by dsimp [K]; rw [mul_pow]; ring
  rw [cubicThetaCircleSeries_coefficient ha]
  change ‖(∑' n, a n*fourierCoeff (cubicThetaCirclePhase (w n) r) (k:ℤ))-
    D*(∑' n, a n*w n^k)‖≤_
  rw [←tsum_mul_left,←hsF.tsum_sub hsM]
  calc
    _ ≤ ∑' n, ‖a n*fourierCoeff (cubicThetaCirclePhase (w n) r) (k:ℤ)-D*(a n*w n^k)‖ :=
      norm_tsum_le_tsum_norm (hsF.sub hsM).norm
    _ ≤ ∑' n, K*(‖a n‖*‖w n‖^(k+1)) :=
      Summable.tsum_le_tsum hB (hsF.sub hsM).norm (hk1.mul_left K)
    _ = _ := tsum_mul_left

end CubicFirstMoment

end

end OAI
