import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedGaussExplicit

namespace OAI

/-! Continue the actual translated-cusp Dirichlet coefficients through
the already proved primary family. No cusp transform is postulated. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaRegularizedShiftedFrequency (b : ℤ) (h : Eisenstein) (s : ℂ) : ℂ :=
  if (3:Eisenstein) ∣ h-lambdaE*(b:Eisenstein) then
    9*cubicThetaRegularizedPrimaryOne (lambdaE*h) s else 0

lemma cubicThetaRegularizedShiftedFrequency_analytic (b : ℤ) {h : Eisenstein}
    (hh : h≠0) :
    AnalyticOnNhd ℂ (cubicThetaRegularizedShiftedFrequency b h) {s : ℂ | 1<s.re} := by
  unfold cubicThetaRegularizedShiftedFrequency
  split_ifs
  · exact analyticOnNhd_const.mul
      (cubicThetaRegularizedPrimaryOne_analytic (mul_ne_zero lambdaE_prime.ne_zero hh))
  · exact analyticOnNhd_const

lemma cubicThetaRegularizedShiftedFrequency_right (a b : ℤ) {h : Eisenstein}
    (hh : h≠0) {s : ℂ} (hs : 3<s.re) :
    cubicThetaRegularizedShiftedFrequency b h s=
      (s-4/3)*cubicThetaShiftedFrequencyDirichlet ((a:Eisenstein)+b*omegaE) h s := by
  rw [cubicThetaShiftedFrequencyDirichlet_eq]
  unfold cubicThetaRegularizedShiftedFrequency
  split_ifs
  · rw [cubicThetaRegularizedPrimaryOne_right (mul_ne_zero lambdaE_prime.ne_zero hh) hs,
      ←cubicThetaPrimaryFourierSeries_two_shift]
    ring
  · simp only [mul_zero]

lemma cubicThetaRegularizedShiftedFrequency_pole (b : ℤ) {h : Eisenstein}
    (hh : h≠0) :
    cubicThetaRegularizedShiftedFrequency b h (4/3)=
      if (3:Eisenstein) ∣ h-lambdaE*(b:Eisenstein) then
        9*cubicThetaArithmeticFourierResidue (lambdaE*h) (4/3) else 0 := by
  unfold cubicThetaRegularizedShiftedFrequency
  split_ifs
  · rw [cubicThetaRegularizedPrimaryOne_residue_eq (mul_ne_zero lambdaE_prime.ne_zero hh)]
  · rfl

end CubicFirstMoment

end

end OAI
