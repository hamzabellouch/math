import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.InfiniteSum.Module

namespace OAI
noncomputable section
namespace CuntzPureness
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem weighted_operator_series_apply [CompleteSpace E] (w : ℕ → 𝕜) (P : ℕ → E →L[𝕜] E)
    (hs : Summable (fun k => w k • P k)) (z : E) (j : ℕ)
    (hp : ∀ k, P k z = if k = j then z else 0) :
    (∑' k, w k • P k) z = w j • z := by
  have hterm (k : ℕ) : (ContinuousLinearMap.apply 𝕜 E z) (w k • P k) =
      if k = j then w j • z else 0 := by
    change w k • P k z = _
    rw [hp k]
    by_cases hk : k = j
    · subst k; simp
    · simp [hk]
  exact ((ContinuousLinearMap.apply 𝕜 E z).map_tsum hs).trans
    ((tsum_congr hterm).trans (tsum_ite_eq j (fun _ => w j • z)))
end CuntzPureness

end

end OAI
