import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleFrequencyJet
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBSqrtApproximation

namespace OAI

/-! The real forbidden action decreases toward its endpoint. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralLiouville_action_antitone (h b eta omega gamma R E : ℝ)
    (hR : 0 < R)
    (hF : ∀ t ∈ Icc R E, 0 < (-1)*homogeneousSpectralLocalizationFrequency h b eta omega t) :
    let p := spectralLiouvilleMomentum (-1) h b eta omega gamma
    AntitoneOn (fun r => (∫ t in r..E, p t).re) (Icc R E) := by
  let p := spectralLiouvilleMomentum (-1) h b eta omega gamma
  have hpc : ContinuousOn p (Icc R E) := fun t ht =>
    (spectralLiouvilleMomentum_hasDerivAt (-1) h b eta omega gamma t
      (hR.trans_le ht.1) (hF t ht)).continuousAt.continuousWithinAt
  change AntitoneOn (fun r => (∫ t in r..E, p t).re) (Icc R E)
  intro r hr s hs hrs
  have hi₁ : IntervalIntegrable p volume r s :=
    (hpc.mono (Icc_subset_Icc hr.1 hs.2)).intervalIntegrable_of_Icc hrs
  have hi₂ : IntervalIntegrable p volume s E :=
    (hpc.mono (Icc_subset_Icc hs.1 le_rfl)).intervalIntegrable_of_Icc hs.2
  have he := congrArg Complex.re (intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂)
  have hn : 0 ≤ (∫ t in r..s, p t).re := by
    have heRe : (∫ t in r..s, p t).re = ∫ t in r..s, (p t).re :=
      (intervalIntegral.intervalIntegral_re hi₁).symm
    rw [heRe]
    exact intervalIntegral.integral_nonneg hrs (fun t _ => spectralComplexSqrt_re_nonneg _)
  simp only [Complex.add_re] at he
  change (∫ t in s..E, p t).re ≤ (∫ t in r..E, p t).re
  linarith

end DefocusingNLS

end OAI
