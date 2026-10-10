import OAI.Analysis.BernoulliCone.GlobalMinimizer

namespace OAI

section
noncomputable section
namespace Bernoulli
open scoped _root_.Bernoulli

theorem nonflat_in_seven : ∃ u : Space 7 → ℝ,
    GlobalMinimizer u ∧ Nonzero u ∧ OneHomogeneous u ∧ ¬ Flat u :=
  DeSilvaJerison.exists_nonflat_dimension_seven
end Bernoulli

end
end

end OAI
