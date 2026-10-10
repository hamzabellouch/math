import OAI.Analysis.Laughlin.FourBody.PairTarget

namespace OAI

namespace Laughlin.Fock
open Filter
open scoped BigOperators Topology

theorem physical_fourBody_estimate :
    ∃ e : ℕ → ℝ, (∀ Q, 0 ≤ e Q) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ Q : ℕ, 25 ≤ Q → ∀ x : Space Q,
        sourceA4Form Q x ≤
          (∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
            occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x))) +
          (10946*(3/10^6 : ℝ)+e Q)*sourceFockEnergy Q x :=
  ⟨averagedFourTransferError,averagedFourTransferError_nonneg,
    averagedFourTransferError_tendsto,sourceA4Form_bound⟩

end Laughlin.Fock

end OAI
