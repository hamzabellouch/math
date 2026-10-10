import Mathlib
import OAI.Probability.SKBarriers.Interpolation.AdaptiveODEExistence

namespace OAI

section

section
noncomputable section
open scoped BigOperators NNReal
open Set Metric
namespace SK.Analytic

theorem exists_positive_adaptive_path {k : ℕ}
    (R : (ℝ × (Fin (k+1) → ℝ)) → (Fin (k+1) → ℝ)) (hR : ContDiff ℝ 1 R)
    (hRb : ∀ p j, R p j ∈ Icc (0:ℝ) 1) (hRm : ∀ p, Monotone (R p))
    (η : ℝ) (hη : 0 < η) :
    ∃ q : ℝ → (Fin (k+1) → ℝ),
      q 0 = (fun j => ((j.val:ℝ)+1)*η) ∧
      (∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt q
        (R (Real.sqrt (1-t),fun j => Real.sqrt (cumulativeGapMap k (q t) j))) (Icc (0:ℝ) 1) t) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ j, η ≤ cumulativeGapMap k (q t) j) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ j, q t j ≤ ((j.val:ℝ)+1)*η+t) := by
  let q₀ : Fin (k+1) → ℝ := fun j => ((j.val:ℝ)+1)*η
  let ε := η/2
  obtain ⟨q,hq0,hq⟩ := exists_floored_adaptive_path R hR hRb ε (by dsimp [ε]; positivity) q₀
  let v := fun t => R (Real.sqrt (1-t),positiveGapScales k ε (q t))
  have hGap0 (j : Fin (k+1)) : cumulativeGapMap k q₀ j = η := by
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [q₀]
    · simp only [cumulativeGapMap_succ,q₀,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
      ring
  have hGapD (j : Fin (k+1)) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt (fun u => cumulativeGapMap k (q u) j)
        (cumulativeGapMap k (v t) j) (Icc (0:ℝ) 1) t := by
    exact ((ContinuousLinearMap.proj j).comp (cumulativeGapMap k)).hasFDerivAt.comp_hasDerivWithinAt t (hq t ht)
  have hGapV (t : ℝ) (j : Fin (k+1)) : 0 ≤ cumulativeGapMap k (v t) j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · exact (hRb _ 0).1
    · change 0 ≤ v t i.succ-v t i.castSucc
      exact sub_nonneg.mpr (hRm _ (Fin.castSucc_le_succ i))
  have hGap (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (j : Fin (k+1)) :
      η ≤ cumulativeGapMap k (q t) j := by
    have H := monotoneOn_unit_of_deriv_nonneg (hGapD j) (fun t _ => hGapV t j)
      (show (0:ℝ) ∈ Icc 0 1 by norm_num) ht ht.1
    change cumulativeGapMap k (q 0) j ≤ cumulativeGapMap k (q t) j at H
    rwa [hq0,hGap0] at H
  have hscales (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      positiveGapScales k ε (q t) = fun j => Real.sqrt (cumulativeGapMap k (q t) j) := by
    funext j
    rw [positiveGapScales,max_eq_right]
    exact (by dsimp [ε]; linarith : ε ≤ η).trans (hGap t ht j)
  refine ⟨q,hq0,?_,hGap,?_⟩
  · intro t ht
    simpa only [hscales t ht] using hq t ht
  · intro t ht j
    have hD (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
        HasDerivWithinAt (fun s => s-q s j) (1-v u j) (Icc (0:ℝ) 1) u := by
      exact (hasDerivWithinAt_id u _).sub
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k+1) => ℝ) j).hasFDerivAt.comp_hasDerivWithinAt u (hq u hu))
    have H := monotoneOn_unit_of_deriv_nonneg hD (fun u _ => sub_nonneg.mpr (hRb _ j).2)
      (show (0:ℝ) ∈ Icc 0 1 by norm_num) ht ht.1
    change 0-q 0 j ≤ t-q t j at H
    rw [hq0] at H
    change 0-((j.val:ℝ)+1)*η ≤ t-q t j at H
    linarith
end SK.Analytic

end
end

end

end OAI
