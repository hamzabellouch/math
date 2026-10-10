import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierTransform
import OAI.NumberTheory.CubicMoment.Estimates.CubicWhittakerMellin
import OAI.NumberTheory.CubicMoment.Estimates.GaussianMellin

namespace OAI

/-! The Fourier heat kernel at the cubic Eisenstein pole s=4/3.
The resulting Bessel function is the literal kernel already used in theta. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicTheta_cubicPole_heat {A v : ℝ} (hA : 0 < A) (hv : 0 < v) :
    (∫ t in Ioi (0:ℝ), ((t^(-2/3:ℝ):ℝ):ℂ)*
      (Real.exp (-v^2*t-A/t):ℂ)) =
      ((A^(1/3:ℝ)/(A*v^2)^(1/6:ℝ):ℝ):ℂ)*
        (cubicBesselKernel (A*v^2):ℂ) := by
  let H : ℝ → ℂ := fun u => (Real.exp (-u)*Real.exp (-(A*v^2)/u):ℝ)
  have hc := inverse_mellin_change H (4/3) hA
  have hleft : (∫ t in Ioi (0:ℝ), ((t^(-2/3:ℝ):ℝ):ℂ)*
      (Real.exp (-v^2*t-A/t):ℂ)) =
      ∫ t in Ioi (0:ℝ), ((t^((4/3:ℝ)-2):ℝ):ℂ)*H (A/t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have he : -(A*v^2)/(A/t) = -v^2*t := by field_simp
    dsimp only [H]
    rw [he, ← Real.exp_add]
    rw [show (4/3:ℝ)-2 = -2/3 by norm_num]
    congr 2
    ring_nf
  rw [hleft, hc]
  have hright : (∫ u in Ioi (0:ℝ), ((u^(-(4/3:ℝ)):ℝ):ℂ)*H u) =
      ((∫ u in Ioi (0:ℝ), cubicBesselHeat (A*v^2) u):ℝ) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only [H, cubicBesselHeat]
    push_cast
    norm_num only [neg_div]
    ring
  rw [hright]
  have hx : (A*v^2)^(1/6:ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (mul_pos hA (sq_pos_of_pos hv)) _)
  unfold cubicBesselKernel
  norm_num only
  push_cast
  field_simp

theorem cubicThetaHyperbolicKernel_fourier_cubicPole {v : ℝ} (hv : 0 < v)
    {w : ℂ} (hw : w ≠ 0) :
    Complex.Gamma (4/3)*traceFourier (cubicThetaHyperbolicKernel v (4/3)) w =
      (Real.pi:ℂ)*
        (((4*Real.pi^2*Complex.normSq w)^(1/3:ℝ)/
          (4*Real.pi^2*Complex.normSq w*v^2)^(1/6:ℝ):ℝ):ℂ)*
        (cubicBesselKernel (4*Real.pi^2*Complex.normSq w*v^2):ℂ) := by
  rw [cubicThetaHyperbolicKernel_fourier hv (by norm_num : 1 < (4/3:ℂ).re)]
  have hi : (∫ t in Ioi (0:ℝ), (t:ℂ)^((4/3:ℂ)-2)*
      Complex.exp ((-v^2*t-4*Real.pi^2*Complex.normSq w/t:ℝ):ℂ)) =
      ∫ t in Ioi (0:ℝ), ((t^(-2/3:ℝ):ℝ):ℂ)*
        (Real.exp (-v^2*t-(4*Real.pi^2*Complex.normSq w)/t):ℂ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [Complex.ofReal_cpow ht.le, Complex.ofReal_exp]
    congr 2
    norm_num
  rw [hi, cubicTheta_cubicPole_heat (by positivity [Complex.normSq_pos.mpr hw]) hv]
  ring

theorem cubicThetaHyperbolicKernel_fourier_whittaker {v : ℝ} (hv : 0 < v)
    {w : ℂ} (hw : w ≠ 0) :
    Complex.Gamma (4/3)*traceFourier (cubicThetaHyperbolicKernel v (4/3)) w =
      (((2*Real.pi*(4*Real.pi^2*Complex.normSq w)^(1/3:ℝ))/
        ((4*Real.pi^2*Complex.normSq w*v^2)^(1/6:ℝ)*(‖w‖*v)):ℝ):ℂ)*
        cubicThetaWhittaker (‖w‖*v) := by
  rw [cubicThetaHyperbolicKernel_fourier_cubicPole hv hw]
  have he : 4*Real.pi^2*Complex.normSq w*v^2 = (2*Real.pi*(‖w‖*v))^2 := by
    rw [Complex.normSq_eq_norm_sq]
    ring
  rw [he, cubicThetaWhittaker]
  have hn : (‖w‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)
  have hvC : (v:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  push_cast
  field_simp [hn, hvC]

end CubicFirstMoment

end

end OAI
