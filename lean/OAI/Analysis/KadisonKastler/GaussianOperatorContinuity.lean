import OAI.Analysis.KadisonKastler.GaussianStateDerivative
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # Norm continuity of Gaussian-smeared operator orbits

The uniform derivative bound upgrades the existing vectorwise analytic
construction to operator norm continuity. This is the smoothing step
needed to integrate an invariant, possibly nonnormal, state.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem gaussianDerivativeEnvelope_nonneg {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (t : ℝ) : 0 ≤ gaussianDerivativeEnvelope r R t := by
  unfold gaussianDerivativeEnvelope
  positivity

theorem gaussianStateAverage_norm_sub_le (a : H →L[ℂ] H) {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) {z w : ℂ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    ‖gaussianStateAverage U hU a r hr w-gaussianStateAverage U hU a r hr z‖ ≤
      ((∫ t : ℝ, gaussianDerivativeEnvelope r R t)*‖a‖)*‖w-z‖ := by
  let C := (∫ t : ℝ, gaussianDerivativeEnvelope r R t)*‖a‖
  have hC : 0 ≤ C := mul_nonneg
    (integral_nonneg (gaussianDerivativeEnvelope_nonneg hr hR)) (norm_nonneg a)
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _))
  intro x
  have hd (v : ℂ) : HasFDerivWithinAt
      (fun v => gaussianStateAverage U hU a r hr v x)
      (ContinuousLinearMap.toSpanSingleton ℂ (gaussianStateAverageDeriv U hU a r hr v x))
      (Metric.closedBall 0 R) v :=
    (gaussianStateAverage_hasDerivAt U hU a r hr v x).hasFDerivAt.hasFDerivWithinAt
  have hb (v : ℂ) (hv : v ∈ Metric.closedBall 0 R) :
      ‖ContinuousLinearMap.toSpanSingleton ℂ (gaussianStateAverageDeriv U hU a r hr v x)‖ ≤
        C*‖x‖ := by
    rw [ContinuousLinearMap.norm_toSpanSingleton]
    exact ((gaussianStateAverageDeriv U hU a r hr v).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right
        (gaussianStateAverageDeriv_norm_le U hU a r hr R hR v
          (by simpa only [Metric.mem_closedBall,dist_zero_right] using hv)) (norm_nonneg x))
  have hh := (convex_closedBall (0 : ℂ) R).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun v _ => hd v) hb
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hw)
  change ‖gaussianStateAverage U hU a r hr w x-gaussianStateAverage U hU a r hr z x‖ ≤ _
  exact hh.trans_eq (by ring)

theorem gaussianStateAverage_continuous (a : H →L[ℂ] H) {r : ℝ} (hr : 0 < r) :
    Continuous (fun z : ℂ => gaussianStateAverage U hU a r hr z) := by
  rw [continuous_iff_continuousAt]
  intro z
  let R := ‖z‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let C := (∫ t : ℝ, gaussianDerivativeEnvelope r R t)*‖a‖
  have hC : 0 ≤ C := mul_nonneg
    (integral_nonneg (gaussianDerivativeEnvelope_nonneg hr hR)) (norm_nonneg a)
  let K : NNReal := ⟨C,hC⟩
  have hK : (K : ℝ)=C := rfl
  have hLip : LipschitzOnWith K (fun w : ℂ => gaussianStateAverage U hU a r hr w)
      (Metric.closedBall 0 R) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro x hx y hy
    rw [hK]
    exact gaussianStateAverage_norm_sub_le U hU a hr hR
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy)
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)
  exact hLip.continuousOn.continuousAt (Metric.closedBall_mem_nhds_of_mem
    (by change dist z 0 < ‖z‖+1; rw [dist_zero_right]; linarith))

end

end KadisonKastler

end OAI
