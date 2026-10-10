import Mathlib
import OAI.Computability.MaxCut.Encoding.MatrixGapInverse
import OAI.Computability.MaxCut.Games.ShortcodeFiberSampling

namespace OAI

/-! The fixed finite matrix reduction obtained from the actual v2 latent
gadget, dimension-uniform shortcode inverse, sparse full-table law and private
local decoder. The construction precedes the parity input and its accuracy.
No inverse, noise, spectral, or decoder certificate is supplied as a premise. -/

namespace MaxCutGames.Decoder.MatrixGap

theorem exists_parameters (p : ℚ) (hp : 0 < p) : Nonempty (Parameters p) :=
  parameters_of_inverse Inverse.ShortcodeTheorem.inversePrinciple p hp

end MaxCutGames.Decoder.MatrixGap

end OAI
