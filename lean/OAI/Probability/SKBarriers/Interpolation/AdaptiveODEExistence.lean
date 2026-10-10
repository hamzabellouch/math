import Mathlib
import OAI.Probability.SKBarriers.Interpolation.AdaptiveODERegular

namespace OAI

section

section
noncomputable section
open scoped BigOperators NNReal
open Set Metric
namespace SK.Analytic

theorem exists_floored_adaptive_path {k : ℕ}
    (R : (ℝ × (Fin (k+1) → ℝ)) → (Fin (k+1) → ℝ)) (hR : ContDiff ℝ 1 R)
    (hRb : ∀ p j, R p j ∈ Icc (0:ℝ) 1)
    (ε : ℝ) (hε : 0 < ε) (q₀ : Fin (k+1) → ℝ) :
    ∃ q : ℝ → (Fin (k+1) → ℝ), q 0 = q₀ ∧
      ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt q
        (R (Real.sqrt (1-t),positiveGapScales k ε (q t))) (Icc (0:ℝ) 1) t := by
  let G := fun p : ℝ × (Fin (k+1) → ℝ) => R (p.1,positiveGapScales k ε p.2)
  have hG : LocallyLipschitz G := regular_positiveGapScales R hR ε hε
  obtain ⟨K,hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_Icc.prod (isCompact_closedBall q₀ 1)) hG.locallyLipschitzOn
  have hs (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : Real.sqrt (1-t) ∈ Icc (0:ℝ) 1 := by
    refine ⟨Real.sqrt_nonneg _,?_⟩
    apply Real.sqrt_le_one.mpr
    linarith [ht.1]
  let F := fun t q => G (Real.sqrt (1-t),q)
  have hf : IsPicardLindelof F (⟨0,by norm_num⟩ : Icc (0:ℝ) 1) q₀ 1 0 1 K := by
    constructor
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      simpa only [F,Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using
        hK.dist_le_mul (Real.sqrt (1-t),x) ⟨hs t ht,hx⟩
          (Real.sqrt (1-t),y) ⟨hs t ht,hy⟩
    · intro x _
      exact (hG.continuous.comp ((Real.continuous_sqrt.comp
        (continuous_const.sub continuous_id)).prodMk continuous_const)).continuousOn
    · intro t _ x _
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
      intro j
      rw [Real.norm_eq_abs,abs_of_nonneg (hRb _ j).1]
      exact (hRb _ j).2
    · norm_num
  exact hf.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

theorem monotoneOn_unit_of_deriv_nonneg {f g : ℝ → ℝ}
    (hf : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt f (g t) (Icc (0:ℝ) 1) t)
    (hg : ∀ t ∈ Icc (0:ℝ) 1, 0 ≤ g t) : MonotoneOn f (Icc (0:ℝ) 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    (fun t ht => (hf t ht).continuousWithinAt)
  · intro t ht
    exact (hf t (interior_subset ht)).mono interior_subset
  · intro t ht
    exact hg t (interior_subset ht)
end SK.Analytic

end
end

end

end OAI
