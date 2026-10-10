import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSeries

namespace OAI

/-! Locally uniform convergence and continuity of the actual cusp Fourier
series in horizontal position and positive height. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaNonconstant (a : Eisenstein → ℂ) (p : ℂ × ℝ) : ℂ :=
  ∑' n : Eisenstein, cubicThetaSeriesTerm a p.1 p.2 n

lemma cubicThetaSeriesTerm_continuousAt (a : Eisenstein → ℂ) (n : Eisenstein)
    {p : ℂ × ℝ} (hp : 0 < p.2) :
    ContinuousAt (fun q : ℂ × ℝ => cubicThetaSeriesTerm a q.1 q.2 n) p := by
  by_cases hn : n = 0
  · simp only [cubicThetaSeriesTerm,hn,ite_true]
    exact continuousAt_const
  · simp only [cubicThetaSeriesTerm,hn,ite_false]
    have hw : ContinuousAt (fun q : ℂ × ℝ =>
        cubicThetaWhittaker (‖cubicThetaFrequency n‖*q.2)) p :=
      (cubicThetaWhittaker_continuousAt (mul_pos (cubicThetaFrequency_pos hn) hp)).comp
        (f := fun q : ℂ × ℝ => ‖cubicThetaFrequency n‖*q.2) (by fun_prop)
    have he : ContinuousAt (fun q : ℂ × ℝ =>
        (Real.fourierChar (tracePair (cubicThetaFrequency n) q.1):ℂ)) p := by
      unfold tracePair
      fun_prop
    exact (continuousAt_const.mul hw).mul he

lemma cubicThetaNonconstant_continuousOn_strip {a : Eisenstein → ℂ} {C b : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (hb : 0 < b) :
    ContinuousOn (cubicThetaNonconstant a) {p : ℂ × ℝ | b < p.2} := by
  let K := C*cubicWhittakerPowerConstant 3*81^(7/3:ℝ)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hC
    (cubicWhittakerPowerConstant_pos (by omega : 1 ≤ 3)).le) (by positivity)
  have hs := (summable_eisenstein_norm_rpow (by norm_num : (1:ℝ) < 4/3)).mul_left
    (K*b^(-14/3:ℝ))
  apply continuousOn_tsum
    (fun n p hp => (cubicThetaSeriesTerm_continuousAt a n (hb.trans hp)).continuousWithinAt) hs
  intro n p hp
  change b < p.2 at hp
  have hpower : p.2^(-14/3:ℝ) ≤ b^(-14/3:ℝ) :=
    Real.rpow_le_rpow_of_nonpos hb hp.le (by norm_num)
  calc
    _ ≤ (K*p.2^(-14/3:ℝ))*norm n^(-4/3:ℝ) :=
      cubicThetaSeriesTerm_bound hC ha (hb.trans hp) p.1 n
    _ ≤ _ := by
      simpa only [neg_div] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower hK)
          (Real.rpow_nonneg (norm_nonneg n) (-4/3:ℝ))

/-- The Fourier series defines a continuous function on hyperbolic 3-space. -/
theorem cubicThetaNonconstant_continuousAt {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    {p : ℂ × ℝ} (hp : 0 < p.2) : ContinuousAt (cubicThetaNonconstant a) p := by
  have hs := cubicThetaNonconstant_continuousOn_strip hC ha
    (show 0 < p.2/2 by positivity)
  have ho : IsOpen {q : ℂ × ℝ | p.2/2 < q.2} := isOpen_lt continuous_const continuous_snd
  exact hs.continuousAt (ho.mem_nhds (by change p.2/2 < p.2; linarith))

end CubicFirstMoment

end

end OAI
