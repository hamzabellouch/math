import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRemovableResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFrequencyResidue

namespace OAI

/-! The actual arithmetic nonzero-frequency coefficient has no spurious
pole on the real interval (1,2). -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

lemma cubicThetaArithmeticFourierResidue_zero (h : Eisenstein) {σ : ℝ}
    (hσ : 1<σ) (hσ2 : σ<2) (hne : (σ:ℂ)≠4/3) :
    cubicThetaArithmeticFourierResidue h σ=0 := by
  simp only [cubicThetaArithmeticFourierResidue,
    cubicThetaArithmeticResidueEnergy_vanishes hσ hσ2 hne,map_zero,inner_zero_right,mul_zero]

theorem cubicThetaFrequencyContinuation_removable {h : Eisenstein} (hh : h≠0)
    {σ : ℝ} (hσ : 1<σ) (hσ2 : σ<2) (hne : (σ:ℂ)≠4/3) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (σ:ℂ) ∧
      cubicThetaFrequencyContinuation h=ᶠ[𝓝[≠] (σ:ℂ)] g := by
  apply cubicThetaSimpleResidue_removable
    (cubicThetaFrequencyContinuation_meromorphic hh (by simpa using hσ))
  have ht := cubicThetaFrequencyContinuation_residue hh hσ hσ2
  rw [cubicThetaArithmeticFourierResidue_zero h hσ hσ2 hne] at ht
  simpa only [smul_eq_mul] using ht

end CubicFirstMoment

end

end OAI
