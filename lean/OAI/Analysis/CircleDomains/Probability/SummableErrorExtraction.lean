import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

/-! A vanishing nonnegative error has an explicit summable extraction.
The selected indices still tend to infinity. -/
open Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_summable_error_extraction {b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (ht : Tendsto b atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, Tendsto s atTop atTop ∧ Summable (fun n => b (s n)) := by
  have hex (j : ℕ) : ∃ n, j ≤ n ∧ b n ≤ (1/2 : ℝ)^j := by
    have hs := ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < (1/2 : ℝ)^j))
    obtain ⟨n, hn, hn'⟩ := ((eventually_ge_atTop j).and hs).exists
    exact ⟨n, hn, hn'.le⟩
  choose s hs he using hex
  refine ⟨s, tendsto_atTop_mono hs tendsto_id, ?_⟩
  exact Summable.of_nonneg_of_le (fun n => hb (s n)) he
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

end CircleDomainRigidity

end

end OAI
