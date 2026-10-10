import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedTrace

namespace OAI

/-! Continue the actual middle primary twist by dividing the explicit
ramified correction. Its residue is derived from actual Fourier residues. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRamifiedCubeFactor_ne_zero (s : ℂ) :
    cubicThetaRamifiedCubeFactor s≠0 := by
  unfold cubicThetaRamifiedCubeFactor
  exact mul_ne_zero (by norm_num)
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))

def cubicThetaRegularizedPrimaryOne (h : Eisenstein) (s : ℂ) : ℂ :=
  cubicThetaRegularizedRamifiedLow h s/
    (cubicThetaRamifiedCubeFactor s*cubicThetaRamifiedTrace h)

theorem cubicThetaRegularizedPrimaryOne_analytic {h : Eisenstein} (hh : h≠0) :
    AnalyticOnNhd ℂ (cubicThetaRegularizedPrimaryOne h) {s : ℂ | 1<s.re} := by
  intro s hs
  exact (cubicThetaRegularizedRamifiedLow_analytic hh s hs).div
    ((cubicThetaRamifiedCubeFactor_analytic s).mul analyticAt_const)
    (mul_ne_zero (cubicThetaRamifiedCubeFactor_ne_zero s) (cubicThetaRamifiedTrace_ne_zero h))

theorem cubicThetaRegularizedPrimaryOne_right {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 3<s.re) :
    cubicThetaRegularizedPrimaryOne h s=(s-4/3)*cubicThetaPrimaryFourierSeries 1 1 s h := by
  unfold cubicThetaRegularizedPrimaryOne
  rw [cubicThetaRegularizedRamifiedLow_right hh hs,cubicThetaRamifiedLowDirichlet_factor]
  have hq := cubicThetaRamifiedCubeFactor_ne_zero s
  have ht := cubicThetaRamifiedTrace_ne_zero h
  field_simp

theorem cubicThetaRegularizedPrimaryOne_pole {h : Eisenstein} (hh : h≠0) :
    cubicThetaRegularizedPrimaryOne h (4/3)=
      (3*cubicThetaArithmeticFourierResidue (lambdaE^3*h) (4/3)-
        cubicThetaArithmeticFourierResidue h (4/3))/cubicThetaRamifiedTrace h := by
  rw [cubicThetaRegularizedPrimaryOne,cubicThetaRegularizedRamifiedLow_pole hh,
    cubicThetaRamifiedCubeFactor_pole]
  ring

end CubicFirstMoment

end

end OAI
