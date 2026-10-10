import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGridAnalytic
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinHolomorphic

namespace OAI

/-! A common summable majorant for the literal grid, uniform in a
positive-height region with bounded height constant. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaGridDecay (s : ℂ) (cd : Eisenstein × Eisenstein) : ℝ :=
  (1+norm cd.1)^(-s.re/2)*(1+norm cd.2)^(-s.re/2)

lemma cubicThetaGridDecay_nonneg (s : ℂ) (cd : Eisenstein × Eisenstein) :
    0 ≤ cubicThetaGridDecay s cd := by
  unfold cubicThetaGridDecay
  exact mul_nonneg (Real.rpow_nonneg (by linarith [norm_nonneg cd.1]) _)
    (Real.rpow_nonneg (by linarith [norm_nonneg cd.2]) _)

lemma cubicThetaGridDecay_summable {s : ℂ} (hs : 2<s.re) :
    Summable (cubicThetaGridDecay s) := by
  have h := summable_eisenstein_one_add_norm (show 1<s.re/2 by linarith)
  change Summable (fun cd : Eisenstein × Eisenstein =>
    (1+norm cd.1)^(-s.re/2)*(1+norm cd.2)^(-s.re/2))
  simpa only [neg_div] using summable_mul_of_summable_norm h.norm h.norm

theorem cubicThetaEisensteinGridTerm_bound (cd : Eisenstein × Eisenstein)
    {p : ℂ × ℝ} (hp : 0<p.2) {s : ℂ} (hs : 2<s.re) :
    ‖cubicThetaEisensteinGridTerm cd p s‖ ≤
      (p.2*cubicThetaHeightConstant p)^s.re*cubicThetaGridDecay s cd := by
  by_cases hc : cubicThetaAdmissiblePair cd
  · have h := cubicThetaEisensteinTerm_bound (cubicThetaBottomRowEquiv.symm ⟨cd,hc⟩) hp hs
    rw [←cubicThetaEisensteinGridTerm_admissible ⟨cd,hc⟩] at h
    exact h
  · simp only [cubicThetaEisensteinGridTerm,hc,ite_false,norm_zero]
    exact mul_nonneg (Real.rpow_nonneg (mul_pos hp (cubicThetaHeightConstant_pos hp)).le _)
      (cubicThetaGridDecay_nonneg s cd)

lemma cubicThetaEisensteinGridTerm_uniform_bound (cd : Eisenstein × Eisenstein)
    {p : ℂ × ℝ} (hp : 0<p.2) {s : ℂ} (hs : 2<s.re) {H : ℝ}
    (hH : p.2*cubicThetaHeightConstant p ≤ H) :
    ‖cubicThetaEisensteinGridTerm cd p s‖ ≤ H^s.re*cubicThetaGridDecay s cd := by
  apply (cubicThetaEisensteinGridTerm_bound cd hp hs).trans
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (mul_pos hp (cubicThetaHeightConstant_pos hp)).le hH (by linarith))
    (cubicThetaGridDecay_nonneg s cd)

end CubicFirstMoment

end

end OAI
