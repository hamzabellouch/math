import OAI.Analysis.CircleDomains.Topology.CollarFragmentSelection

namespace OAI

/-! Limiting fragment budgets only require each fixed finite collection to
exist eventually; no artificial restrictions are imposed on early stages. -/

open Set Function Filter
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem fragment_limit_budget_of_eventually
    (c : ℕ → ℕ → ℝ≥0∞) (c₀ : ℕ → ℝ≥0∞) (A : ℕ → ℝ≥0∞) (A₀ : ℝ≥0∞)
    (hc : ∀j, Tendsto (fun n => c n j) atTop (𝓝 (c₀ j)))
    (hA : Tendsto A atTop (𝓝 A₀))
    (hbudget : ∀F : Finset ℕ, ∀ᶠn in atTop, ∑j ∈ F, c n j ≤ A n) :
    (∑'j, c₀ j) ≤ A₀ := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le fun F => le_of_tendsto_of_tendsto
    (tendsto_finsetSum F (fun j _ => hc j)) hA (hbudget F)

end CircleDomainRigidity

end

end OAI
