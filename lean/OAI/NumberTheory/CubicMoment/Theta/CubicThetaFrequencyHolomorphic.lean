import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowContinuation

namespace OAI

/-! Holomorphy of the actual arithmetic Fourier coefficients on their
initial half-plane, with a common bound independent of the frequency. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequencyTerm_strip_bound {a : ℝ} (ha : 2<a)
    {s : ℂ} (hs : a<s.re) (h c : Eisenstein) :
    ‖cubicThetaFrequencyTerm s h c‖ ≤ 9*(norm c)^(-(a-1)) := by
  by_cases hc : c=0
  · simp only [hc,cubicThetaFrequencyTerm,ne_eq,not_true_eq_false,and_false,ite_false,norm_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _)
  · exact (cubicThetaFrequencyTerm_bound (ha.trans hs) h c).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (one_le_norm hc) (by linarith)) (by norm_num))

lemma cubicThetaFrequencyDirichlet_differentiableOn {a : ℝ} (ha : 2<a)
    (h : Eisenstein) :
    DifferentiableOn ℂ (cubicThetaFrequencyDirichlet h) {s : ℂ | a<s.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    ((summable_eisenstein_norm_rpow (show 1<a-1 by linarith)).mul_left 9)
  · intro c
    exact (cubicThetaFrequencyTerm_entire h c).differentiableOn
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro c s hs
    exact cubicThetaFrequencyTerm_strip_bound ha hs h c

theorem cubicThetaFrequencyDirichlet_differentiableAt (h : Eisenstein)
    {s : ℂ} (hs : 2<s.re) :
    DifferentiableAt ℂ (cubicThetaFrequencyDirichlet h) s := by
  have ha : 2<(2+s.re)/2 := by linarith
  have hU : IsOpen {z : ℂ | (2+s.re)/2<z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ {z : ℂ | (2+s.re)/2<z.re} := by
    change (2+s.re)/2<s.re
    linarith
  exact (cubicThetaFrequencyDirichlet_differentiableOn ha h).differentiableAt
    (hU.mem_nhds hsU)

theorem cubicThetaFrequencyDirichlet_bound (h : Eisenstein) {s : ℂ} (hs : 2<s.re) :
    ‖cubicThetaFrequencyDirichlet h s‖ ≤
      9*(∑' c : Eisenstein, (norm c)^(-(s.re-1))) := by
  have hsum := cubicThetaFrequencyTerm_norm_summable hs h
  calc
    _ ≤ ∑' c : Eisenstein, ‖cubicThetaFrequencyTerm s h c‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' c : Eisenstein, 9*(norm c)^(-(s.re-1)) :=
      hsum.tsum_le_tsum (cubicThetaFrequencyTerm_bound hs h)
        ((summable_eisenstein_norm_rpow (show 1<s.re-1 by linarith)).mul_left 9)
    _ = _ := tsum_mul_left

end CubicFirstMoment

end

end OAI
