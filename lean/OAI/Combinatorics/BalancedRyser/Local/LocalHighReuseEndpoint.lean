import OAI.Combinatorics.BalancedRyser.Incidence.PencilReuseEndpoint
import OAI.Combinatorics.BalancedRyser.Local.LocalHighReuse

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter
open scoped Topology
noncomputable section
universe u

theorem highReuse_uniform_vanishing :
    ∀ K : ℝ, 0 < K → ∃ ε : ℕ → ℝ,
      Tendsto ε atTop (𝓝 0) ∧ (∀ q, 0 ≤ ε q) ∧
      ∃ q₀ : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        q₀ ≤ Fintype.card F → ∀ (Q : Local.RetentionRule F) (w : Local.Kernel F),
        Local.KernelConditions Q w K →
          Local.selectedProbability w Local.HighReuseEvent ≤ ε (Fintype.card F) :=
  Local.HighReuse.uniform_vanishing_of_pencilReuse pencilReuse_proof

end
end Balanced

end OAI
