import OAI.Probability.InvariantIsing.Gaussian.GaussianScaledEmpiricalWeak

namespace OAI

/-! The Gaussian Marchenko–Pastur theorem, including real spectral scaling. -/
noncomputable section
open MeasureTheory ProbabilityTheory
universe u
namespace InvariantIsing

theorem marchenkoPastur_proved (α : ℝ) (hα : 0 < α) : MarchenkoPasturInput.{u} α hα where
  probability := marchenkoPastur_probability hα
  support_bound := marchenkoPastur_support_bound hα
  left_mem := marchenkoPastur_left_mem hα
  right_mem := marchenkoPastur_right_mem hα
  measurable_eigenvalues := fun N => measurable_gaussianPatternEigenvalues N (gaussianPatternCount α N)
  weak := by
    intro Ω _ P _ Z hZ c
    exact gaussianPattern_scaled_empirical_weak hα P Z hZ c

end InvariantIsing

end

end OAI
