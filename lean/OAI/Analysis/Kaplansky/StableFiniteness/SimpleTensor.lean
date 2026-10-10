import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.StableFiniteness.SimpleAmbient
import OAI.Analysis.Kaplansky.StableFiniteness.SimpleReduction

namespace OAI

section
noncomputable section
namespace KaplanskyConsequences

theorem simple_stable_tensor_counterexample_exists : SimpleStableTensorCounterexample :=
  simple_stable_tensor_reduction simple_stablyFinite_traceless_exists

end KaplanskyConsequences
end
end

end OAI
