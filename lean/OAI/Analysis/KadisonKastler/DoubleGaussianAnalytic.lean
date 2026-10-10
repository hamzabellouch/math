import OAI.Analysis.KadisonKastler.DoubleGaussianKMS
import OAI.Analysis.KadisonKastler.MovingGaussianAverage
import OAI.Analysis.KadisonKastler.GaussianNormBounds

namespace OAI

/-! # The entire diagonal of two Gaussian-smoothed actions -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U V : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem doubleGaussianStateAverage_diagonal_differentiable
    (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (x : H) :
    Differentiable ℂ (fun z => doubleGaussianStateAverage U V hU hV a r hr z (-z) x) := by
  intro z
  let B : ℂ → H →L[ℂ] H := fun w => gaussianStateAverage V hV a r hr (-w)
  let B' : ℂ → H →L[ℂ] H := fun w => -gaussianStateAverageDeriv V hV a r hr (-w)
  have hd (w : ℂ) (y : H) : HasDerivAt (fun v => B v y) (B' w y) w := by
    have hh := (gaussianStateAverage_hasDerivAt V hV a r hr (-w) y).scomp w (hasDerivAt_id w).neg
    simpa only [B, B', Function.comp_def, neg_one_smul, neg_apply] using hh
  let R := ‖z‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hnorm {w : ℂ} (hw : w ∈ Metric.ball z 1) : ‖-w‖ ≤ R := by
    have hi : ‖w‖ ≤ ‖z‖ + dist w z := by
      calc
        _ = ‖z + (w - z)‖ := by rw [add_sub_cancel]
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ = _ := by rw [dist_eq_norm]
    have hw' : dist w z < 1 := hw
    rw [norm_neg]
    dsimp [R]
    linarith
  apply gaussianStateAverage_moving_differentiableAt U hU B B' hd r hr z x
    (Real.exp (r * R ^ 2) * Real.sqrt (Real.pi / r) * ‖a‖)
    ((∫ t : ℝ, gaussianDerivativeEnvelope r R t) * ‖a‖)
  · intro w hw
    exact gaussianStateAverage_norm_of_norm_le V hV a r hr R hR (-w) (hnorm hw)
  · intro w hw
    dsimp [B']
    rw [norm_neg]
    exact gaussianStateAverageDeriv_norm_le V hV a r hr R hR (-w) (hnorm hw)

theorem doubleGaussianStateAverage_diagonal_bound
    (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (z : ℂ)
    (hz₀ : 0 ≤ z.im) (hz₁ : z.im ≤ 1) :
    ‖doubleGaussianStateAverage U V hU hV a r hr z (-z)‖ ≤
      (Real.exp r * Real.sqrt (Real.pi / r)) ^ 2 * ‖a‖ := by
  have hzi : |z.im| ≤ 1 := by rw [abs_of_nonneg hz₀]; exact hz₁
  have hni : |(-z).im| ≤ 1 := by simpa only [Complex.neg_im, abs_neg] using hzi
  have hi := gaussianStateAverage_norm_of_im_le V hV a r hr 1 zero_le_one (-z) hni
  have ho := gaussianStateAverage_norm_of_im_le U hU (gaussianStateAverage V hV a r hr (-z))
    r hr 1 zero_le_one z hzi
  simp only [one_pow, mul_one] at hi ho
  apply ho.trans
  calc
    _ ≤ (Real.exp r * Real.sqrt (Real.pi / r)) *
        ((Real.exp r * Real.sqrt (Real.pi / r)) * ‖a‖) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring

end

end KadisonKastler

end OAI
