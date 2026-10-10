import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Regular.ReducedTrace
import OAI.Analysis.Kaplansky.StableFiniteness.TracialStable

namespace OAI

section
noncomputable section
namespace KaplanskyConsequences.Regular
variable {G : Type*} [Group G]

theorem algebra_stablyFinite : StablyFinite (Algebra G) :=
  stablyFinite_of_faithful_trace canonicalTrace coefficient_faithful

end KaplanskyConsequences.Regular
end
end

end OAI
