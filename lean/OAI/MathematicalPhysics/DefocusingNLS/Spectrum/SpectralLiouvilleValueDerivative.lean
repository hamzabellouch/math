import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalLiouvillePair

namespace OAI

/-! The second Liouville coordinate is the actual derivative of the first. -/

namespace DefocusingNLS

theorem spectralLiouville_value_hasDerivAt (h r : ℝ) (hr : 0 < r)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) :
    HasDerivAt (fun t => (homogeneousSpectralLocalizationState h (fun x => (f x,deriv f x)) t).1)
      (homogeneousSpectralLocalizationState h (fun x => (f x,deriv f x)) r).2 r := by
  have hA := homogeneousSpectralLocalizationFactor_hasDerivAt h r hr
  have hd := (hf.differentiable (by norm_num) r).hasDerivAt
  apply (hA.mul hd).congr_deriv
  dsimp only [homogeneousSpectralLocalizationState]
  ring

theorem spectralPhysicalLiouvillePair_value_hasDerivAt (r : ℝ) (hr : 0 < r)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    HasDerivAt (fun t => (spectralPhysicalLiouvillePair f g t).1.1)
      (spectralPhysicalLiouvillePair f g r).1.2 r ∧
    HasDerivAt (fun t => (spectralPhysicalLiouvillePair f g t).2.1)
      (spectralPhysicalLiouvillePair f g r).2.2 r :=
  ⟨spectralLiouville_value_hasDerivAt 1 r hr f hf,
    spectralLiouville_value_hasDerivAt (-1) r hr g hg⟩

end DefocusingNLS

end OAI
