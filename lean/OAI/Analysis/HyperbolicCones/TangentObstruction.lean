import OAI.Analysis.HyperbolicCones.TangentIdentity
import OAI.Analysis.HyperbolicCones.TangentRigidity

namespace OAI

namespace Paper256

theorem NormalizedPencil.impossible (P : NormalizedPencil) : False := by
  obtain ⟨v, T, hv, hv0, hformula⟩ := P.tangent_identity
  exact impossible_of_tangent_formula P v T hv hv0 hformula

end Paper256

end OAI
