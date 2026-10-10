import OAI.Analysis.Pureness.Operators.OperatorSeriesEigenvector

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem weighted_operator_partial_sum_apply (w : ℕ → 𝕜) (P : ℕ → E →L[𝕜] E)
    (z : E) (j m : ℕ) (hp : ∀ k, P k z = if k = j then z else 0) :
    (∑ k ∈ Finset.range m, w k • P k) z = (if j < m then w j else 0) • z := by
  classical
  simp only [sum_apply, smul_apply, hp]
  have he (k : ℕ) : w k • (if k = j then z else 0) =
      if k = j then w j • z else 0 := by
    by_cases hk : k = j
    · subst k; simp
    · simp [hk]
  simp only [he]
  simp [Finset.mem_range, ite_smul]

theorem exists_norm_le_two_of_tendsto {V : Type*} [NormedAddCommGroup V]
    (u : ℕ → V) (v : V) (hc : Tendsto u atTop (nhds v))
    (hv : ‖v‖ ≤ 1) (n : ℕ) : ∃ m, n ≤ m ∧ ‖u m‖ ≤ 2 := by
  have he : ∀ᶠ m in atTop, ‖u m‖ < 2 :=
    hc.norm.eventually_lt_const (lt_of_le_of_lt hv (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  exact ⟨max n N, le_max_left _ _, (hN _ (le_max_right _ _)).le⟩
end CuntzPureness

end

end OAI
