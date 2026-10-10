import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.BlockAdaptivePath
import OAI.Probability.SKBarriers.Interpolation.SKAdaptiveContinuity
import OAI.Probability.SKBarriers.Interpolation.AdaptiveIntegral

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem exists_sk_finite_interpolation {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (hsmall : (k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η)) ≤ 1) :
    ∃ q : ℝ → Fin (k+1) → ℝ,
      q 0 = (fun j => ((j.val:ℝ)+1)*η) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt q (skAdaptiveMean N k β u (q u))
        (Set.Icc (0:ℝ) 1) u) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, ∀ j, η ≤ cumulativeGapMap k (q u) j) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, ∀ j, q u j ≤ ((j.val:ℝ)+1)*η+u) ∧
      skAdaptivePressure N k β (q 1) 1-skAdaptivePressure N k β (q 0) 0 ≤
        (β^2/4)*(-1+2*(q 1 (Fin.last k)-q 0 (Fin.last k))-
          ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(q 1 j-q 0 j)^2+
          20*((k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η))+1/Real.sqrt (k:ℝ))) := by
  obtain ⟨q,h0,hD,hgap,hupper,herr⟩ := exists_block_adaptive_path hN hk
    (skInteraction N) (fun _ => β/Real.sqrt (N:ℝ)) hβ hη hsmall
  have hD' : ∀ u ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt q (skAdaptiveMean N k β u (q u))
      (Set.Icc (0:ℝ) 1) u := by
    simpa only [skAdaptiveMean_eq_block] using hD
  refine ⟨q,h0,hD',hgap,hupper,?_⟩
  have hqc := HasDerivWithinAt.continuousOn hD'
  have hrc := skAdaptiveMean_continuousOn (N := N) β hqc
  apply adaptive_integrated_bound (fun u => skAdaptivePressure N k β (q u) u) q
    (fun u => skAdaptiveMean N k β u (q u))
    (fun u => ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*skAdaptiveError N k β u (q u) j)
    (fun _ => ((k+1:ℕ):ℝ)⁻¹) (fun _ => by positivity) (by positivity)
    (skAdaptivePressure_continuousOn β hqc)
    (fun j => (continuous_apply j).comp_continuousOn hrc) hD'
  · intro u hu
    exact skAdaptivePressure_hasDerivAt hN β q hu.2
      (fun b => hη.trans_le (hgap u ⟨hu.1.le,hu.2.le⟩ b))
      ((hD' u ⟨hu.1.le,hu.2.le⟩).hasDerivAt (Icc_mem_nhds hu.1 hu.2))
  · intro u hu
    have H := herr u ⟨hu.1.le,hu.2.le⟩
    have ha : (fun _ : Fin (Fintype.card (Edge N)) => Real.sqrt (1-u)*(β/Real.sqrt (N:ℝ))) =
        (fun _ => β*Real.sqrt (1-u)/Real.sqrt (N:ℝ)) := by funext i; ring
    dsimp only at H
    simpa only [ha,skAdaptiveError,skAdaptiveExponent] using H
end SK.Analytic

end
end

end

end OAI
