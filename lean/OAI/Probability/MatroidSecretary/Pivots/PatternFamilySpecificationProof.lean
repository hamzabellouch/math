import OAI.Probability.MatroidSecretary.Residual.ResidualFamilySpecification
import OAI.Probability.MatroidSecretary.Residual.ResidualFamilyContract

namespace OAI

namespace MatroidProphet.MainAlgorithm

/-- Thin packaging of the complete, already proved all-witness family theorem. -/
theorem pattern_family_claim : PatternFamilyClaim := by
  intro n M hE κ hκ d s i hsize ε
  exact uniform_residual_family M hE κ hκ d s i hsize ε

end MatroidProphet.MainAlgorithm

end OAI
