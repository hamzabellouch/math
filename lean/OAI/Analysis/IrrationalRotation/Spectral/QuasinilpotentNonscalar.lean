import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace OAI

open Filter
open scoped Topology

namespace InvariantProjection

section Algebra
variable {𝕜 A : Type*} [NormedField 𝕜] [NormedRing A]
  [NormedAlgebra 𝕜 A] [NormOneClass A]

theorem norm_root_smul_one (c : 𝕜) (n : ℕ) (hn : n ≠ 0) :
    ‖(c • (1 : A)) ^ n‖ ^ (1 / (n : ℝ)) = ‖c‖ := by
  rw [smul_pow, one_pow, norm_smul, norm_one, mul_one, norm_pow, one_div]
  exact Real.pow_rpow_inv_natCast (norm_nonneg c) hn

theorem scalar_eq_zero_of_norm_root_tendsto (c : 𝕜)
    (h : Tendsto (fun n : ℕ => ‖(c • (1 : A)) ^ n‖ ^ (1 / (n : ℝ)))
      atTop (𝓝 0)) : c = 0 := by
  have heq : (fun n : ℕ => ‖(c • (1 : A)) ^ n‖ ^ (1 / (n : ℝ)))
      =ᶠ[atTop] fun _ => ‖c‖ := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact norm_root_smul_one c n (Nat.ne_of_gt hn)
  have hc : Tendsto (fun _ : ℕ => ‖c‖) atTop (𝓝 0) := h.congr' heq
  exact norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hc)

theorem not_scalar_of_nonzero_norm_root_tendsto {a : A} (ha : a ≠ 0)
    (h : Tendsto (fun n : ℕ => ‖a ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0)) :
    ∀ c : 𝕜, a ≠ c • (1 : A) := by
  intro c hc
  have hc0 := scalar_eq_zero_of_norm_root_tendsto c (hc ▸ h)
  apply ha
  simpa [hc0] using hc

end Algebra

end InvariantProjection

namespace InvariantProjection

theorem continuousLinearMap_not_scalar_of_nonzero_norm_root_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Nontrivial E]
    {T : E →L[ℂ] E} (hT : T ≠ 0)
    (h : Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0)) :
    ∀ c : ℂ, T ≠ c • (1 : E →L[ℂ] E) := by
  exact not_scalar_of_nonzero_norm_root_tendsto (𝕜 := ℂ) (A := E →L[ℂ] E) hT h

end InvariantProjection

end OAI
