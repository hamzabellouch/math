import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

namespace Yau.Geometry
open Filter
open scoped Topology
lemma eventually_inverse_square_small (C eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, C*((n:ℝ)^2)⁻¹ < eps := by
  have hpow : Tendsto (fun n : ℕ ↦ (n:ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : ℕ ↦ C*((n:ℝ)^2)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hpow).const_mul C
  exact ht.eventually (gt_mem_nhds heps)

end Yau.Geometry

end OAI
