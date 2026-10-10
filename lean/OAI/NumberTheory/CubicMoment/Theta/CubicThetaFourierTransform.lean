import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierHeat

namespace OAI

/-! The exact trace-Fourier transform of the hyperbolic kernel, derived
by the absolutely convergent Gaussian integral. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaHyperbolicKernel (v : ℝ) (s : ℂ) (z : ℂ) : ℂ :=
  ((Complex.normSq z+v^2:ℝ):ℂ)^(-s)

lemma cubicThetaFourierHeat_time {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 0 < s.re) (w z : ℂ) :
    (∫ t in Ioi (0:ℝ), cubicThetaFourierHeat v s w t z) =
      Complex.Gamma s*(Real.fourierChar (-tracePair z w):ℂ)*
        cubicThetaHyperbolicKernel v s z := by
  have hr : 0 < Complex.normSq z+v^2 :=
    add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (sq_pos_of_pos hv)
  calc
    _ = (∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1)*
        Complex.exp (-(((Complex.normSq z+v^2:ℝ):ℂ)*(t:ℂ))))*
          (Real.fourierChar (-tracePair z w):ℂ) := by
      rw [← integral_mul_const]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      unfold cubicThetaFourierHeat
      dsimp only
      rw [← Real.exp_add]
      have he : -v^2*t+-t*‖z‖^2 = -(Complex.normSq z+v^2)*t := by
        rw [Complex.normSq_eq_norm_sq]
        ring
      rw [he, Complex.ofReal_exp]
      push_cast
      ring_nf
    _ = _ := by
      rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr]
      simp only [one_div, Complex.inv_cpow_ofReal_nonneg hr.le,
        ← Complex.cpow_neg, cubicThetaHyperbolicKernel]
      ring

lemma cubicThetaFourierHeat_space (v : ℝ) (s w : ℂ) {t : ℝ}
    (ht : 0 < t) :
    (∫ z : ℂ, cubicThetaFourierHeat v s w t z) =
      (Real.pi:ℂ)*(t:ℂ)^(s-2)*
        Complex.exp ((-v^2*t-4*Real.pi^2*Complex.normSq w/t:ℝ):ℂ) := by
  calc
    _ = ((t:ℂ)^(s-1)*(Real.exp (-v^2*t):ℂ))*
        traceFourier (fun z : ℂ => Complex.exp (-(t:ℂ)*‖z‖^2)) w := by
      rw [traceFourier, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      unfold cubicThetaFourierHeat
      have he : Complex.exp (-(t:ℂ)*‖z‖^2) = (Real.exp (-t*‖z‖^2):ℂ) := by
        rw [Complex.ofReal_exp]
        congr 1
        push_cast
        ring
      rw [he, Complex.ofReal_mul]
      ring
    _ = _ := by
      rw [traceFourier_gaussian ht]
      have hp : (t:ℂ)^(s-1)/(t:ℂ) = (t:ℂ)^(s-2) := by
        calc
          _ = (t:ℂ)^(s-1)/(t:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]
          _ = _ := by
            rw [← Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
            congr 1
            ring
      rw [Complex.ofReal_div]
      calc
        _ = (Real.pi:ℂ)*((t:ℂ)^(s-1)/(t:ℂ))*
            ((Real.exp (-v^2*t):ℂ)*
              Complex.exp ((-4*Real.pi^2/t*Complex.normSq w:ℝ):ℂ)) := by ring
        _ = _ := by
          rw [hp, Complex.ofReal_exp, ← Complex.exp_add]
          congr 2
          push_cast
          ring

theorem cubicThetaHyperbolicKernel_fourier {v : ℝ} (hv : 0 < v) {s : ℂ}
    (hs : 1 < s.re) (w : ℂ) :
    Complex.Gamma s*traceFourier (cubicThetaHyperbolicKernel v s) w =
      (Real.pi:ℂ)*(∫ t in Ioi (0:ℝ), (t:ℂ)^(s-2)*
        Complex.exp ((-v^2*t-4*Real.pi^2*Complex.normSq w/t:ℝ):ℂ)) := by
  calc
    _ = ∫ z : ℂ, ∫ t in Ioi (0:ℝ), cubicThetaFourierHeat v s w t z := by
      simp_rw [cubicThetaFourierHeat_time hv (show 0 < s.re by linarith)]
      rw [traceFourier, ← integral_const_mul]
      congr 1
      funext z
      ring
    _ = ∫ t in Ioi (0:ℝ), ∫ z : ℂ, cubicThetaFourierHeat v s w t z :=
      (integral_integral_swap (cubicThetaFourierHeat_integrable hv hs w)).symm
    _ = _ := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => by simpa only [mul_assoc] using cubicThetaFourierHeat_space v s w ht)

end CubicFirstMoment

end

end OAI
