import OAI.Analysis.MutuallyUnbiased.Certificate.Algebra
import OAI.Analysis.MutuallyUnbiased.Moments.Moments

namespace OAI

namespace MUB6.Certificate

/-- A finite integer exponent matrix, with its dimensions retained. -/
structure ExponentCode where
  rows : ℕ
  columns : ℕ
  entries : Matrix (Fin rows) (Fin columns) ℤ
  deriving Inhabited

/-- The interpretation is the actual injective moment defined in Section 2. -/
noncomputable def ExponentCode.moment (H : CMatrix) (A : ExponentCode) : ℝ :=
  injectiveMoment H A.entries

end MUB6.Certificate

end OAI
