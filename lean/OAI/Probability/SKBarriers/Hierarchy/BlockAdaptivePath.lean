import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.AverageOverlap
import OAI.Probability.SKBarriers.Hierarchy.BlockAdaptiveOverlap
import OAI.Probability.SKBarriers.Interpolation.AdaptivePositivePath

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem exists_block_adaptive_path {D N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (hsmall : (k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η)) ≤ 1) :
    ∃ q : ℝ → (Fin (k+1) → ℝ),
      q 0 = (fun j => ((j.val:ℝ)+1)*η) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt q
        (blockAdaptiveOverlap I a β (Real.sqrt (1-u),fun j => Real.sqrt (cumulativeGapMap k (q u) j)))
          (Set.Icc (0:ℝ) 1) u) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, ∀ j, η ≤ cumulativeGapMap k (q u) j) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, ∀ j, q u j ≤ ((j.val:ℝ)+1)*η+u) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1,
        let U := blockExponent I (fun i => Real.sqrt (1-u)*a i)
          (fun b => β*Real.sqrt (cumulativeGapMap k (q u) b))
        (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹ *
          hierarchyOverlapError (blockDimension D N k) (blockMass D N k) U
            (fun s i => spin (s i)) (blockLevel D N k j)) ≤
          20*((k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η))+1/Real.sqrt (k:ℝ))) := by
  obtain ⟨q,h0,hD,hgap,hupper⟩ := exists_positive_adaptive_path (k := k)
    (blockAdaptiveOverlap I a β) ((blockAdaptiveOverlap_contDiff I a β).of_le (by norm_num))
    (blockAdaptiveOverlap_bounds I a β) (blockAdaptiveOverlap_monotone I a β) η hη
  refine ⟨q,h0,hD,hgap,hupper,?_⟩
  intro u hu
  have hs (b : Fin (k+1)) :
      Real.sqrt (β^2*cumulativeGapMap k (q u) b) = β*Real.sqrt (cumulativeGapMap k (q u) b) := by
    rw [Real.sqrt_mul (sq_nonneg β),Real.sqrt_sq_eq_abs,abs_of_nonneg hβ.le]
  have H := block_average_overlap_concentration hN hk I (fun i => Real.sqrt (1-u)*a i)
    (fun b => β^2*cumulativeGapMap k (q u) b) (by positivity : 0 < β^2*η)
    (fun b => mul_le_mul_of_nonneg_left (hgap u hu b) (sq_nonneg β)) hsmall
  simpa only [hs] using H
end SK.Analytic

end
end

end

end OAI
