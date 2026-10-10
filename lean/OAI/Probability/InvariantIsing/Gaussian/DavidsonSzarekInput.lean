import OAI.Probability.InvariantIsing.Gaussian.GaussianGramEdges
import OAI.Probability.InvariantIsing.Gaussian.GaussianGramUniformIntegrability

namespace OAI

/-! Gaussian spectral edge and uniform-integrability estimates,
proved using the Gaussian Poincaré inequality. -/
noncomputable section
namespace InvariantIsing

theorem davidsonSzarek_proved (α : ℝ) (hα : 0 < α) : DavidsonSzarekInput α hα := by
  constructor
  · intro Ω _ P _ Z hZ c
    exact gaussianPattern_spectralExcess_tendsto hα P Z hZ c
  · intro Ω _ P _ Z hZ c
    exact gaussianPattern_spectralRadius_uniformIntegrable hα.le P Z hZ c

end InvariantIsing

end

end OAI
