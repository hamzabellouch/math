import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridEnergyLemmas
import OAI.Computability.UniqueGames.Inverse.ShortcodeFromGrassmannLemmas

namespace OAI

section

/-! The Grassmann theorem, chart retention, zero-factor correction,
output-fiber extraction, and affine row/column slice construction yield the
unconditional affine matrix inverse theorem. -/

namespace UniqueGamesTheorem.Inverse.ShortcodeTheorem
noncomputable section

/-- Full-factor sampling includes zero. The conclusion retains an affine
intercept and applies to arbitrary matrix labelings without a folding premise. -/
theorem inversePrinciple : Shortcode.InversePrinciple :=
  ShortcodeFromGrassmann.inversePrinciple_of_expansion KMSExpansion.kms_expansion

end
end UniqueGamesTheorem.Inverse.ShortcodeTheorem

end

end OAI
