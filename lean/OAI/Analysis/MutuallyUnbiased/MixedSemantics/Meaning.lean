import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Code
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules

namespace OAI

namespace MUB6.Certificate.MixedSemantics

noncomputable def Code.moment (B : Fin 7 → Basis) (c : Code) : ℝ :=
  mixedMoment B c.matrix c.label

theorem Code.abs_moment_le_one (B : Fin 7 → Basis) (hB : IsMUBFamily B) (c : Code) :
    |c.moment B| ≤ 1 := mixedMoment_abs_le_one B hB _ _

end MUB6.Certificate.MixedSemantics

end OAI
