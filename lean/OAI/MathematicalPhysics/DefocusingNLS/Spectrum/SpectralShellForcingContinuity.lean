import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellMatchedCoupling

namespace OAI

/-! Continuity of the actual two channel forcings on a positive shell. -/

open Set
namespace DefocusingNLS

theorem spectralShellForcing_continuousOn (m : ℕ) (R E : ℝ) (hR : 0<R)
    (Q : ℝ → ℂ) (u : ℝ → (ℂ × ℂ) × (ℂ × ℂ))
    (hQ : ContinuousOn Q (Icc R E)) (hu : ContinuousOn u (Icc R E)) :
    ContinuousOn (fun r => spectralShellPlusForcing m (Q r) r (u r)) (Icc R E) ∧
      ContinuousOn (fun r => spectralShellMinusForcing m (Q r) r (u r)) (Icc R E) := by
  have hfac (h : ℝ) : ContinuousOn (homogeneousSpectralLocalizationFactor h) (Icc R E) := by
    intro r hr
    exact (homogeneousSpectralLocalizationFactor_hasDerivAt h r
      (hR.trans_le hr.1)).continuousAt.continuousWithinAt
  have hne (h r : ℝ) : homogeneousSpectralLocalizationFactor h r≠0 := Complex.exp_ne_zero _
  have hp := (hfac 1).div (hfac (-1)) (fun r _ => hne (-1) r)
  have hm := (hfac (-1)).div (hfac 1) (fun r _ => hne 1 r)
  have hD : ContinuousOn (fun r => spectralDiagonalCoefficient m (Q r)) (Icc R E) := by
    dsimp only [spectralDiagonalCoefficient]
    fun_prop
  have hC : ContinuousOn (fun r => spectralCrossCoefficient m (Q r)) (Icc R E) := by
    dsimp only [spectralCrossCoefficient]
    fun_prop
  constructor
  · exact (hD.mul hu.fst.fst).add ((hC.mul hp).mul hu.snd.fst)
  · exact (hD.star.mul hu.snd.fst).add ((hC.star.mul hm).mul hu.fst.fst)

end DefocusingNLS

end OAI
