import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.SpinParameterMoments
import OAI.Probability.SKBarriers.Hierarchy.AverageMeanVariance

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def blockAdaptiveOverlap {D N k : ℕ} (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (β : ℝ) (p : ℝ × (Fin (k+1) → ℝ)) (j : Fin (k+1)) : ℝ :=
  hierarchyMeanOverlap (blockDimension D N k) (blockMass D N k)
    (blockExponent I (fun i => p.1*a i) (fun b => β*p.2 b))
    (fun i s => spin (s i)) (blockLevel D N k j)

theorem blockCoefficients_contDiff {D N k : ℕ} (a : Fin D → ℝ) (β : ℝ) :
    ContDiff ℝ 2 (fun p : ℝ × (Fin (k+1) → ℝ) =>
      blockCoefficients (N := N) (fun i => p.1*a i) (fun b => β*p.2 b)) := by
  apply contDiff_pi.mpr
  intro t
  refine Fin.addCases (fun i => ?_) (fun i => ?_) t
  · simp only [blockCoefficients,Fin.addCases_left]
    exact contDiff_fst.mul contDiff_const
  · simp only [blockCoefficients,Fin.addCases_right]
    exact contDiff_const.mul ((contDiff_apply ℝ ℝ _).comp contDiff_snd)

theorem blockAdaptiveOverlap_contDiff {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (a : Fin D → ℝ) (β : ℝ) : ContDiff ℝ 2 (blockAdaptiveOverlap (k := k) I a β) := by
  apply contDiff_pi.mpr
  intro j
  exact (spinHierarchyOverlap_contDiff (blockDimension D N k) (blockMass D N k)
    (blockInteraction I) (fun i s => spin (s i)) (fun i s => by cases s i <;> norm_num [spin])
    (blockLevel D N k j)).comp (blockCoefficients_contDiff a β)

theorem blockAdaptiveOverlap_bounds {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (a : Fin D → ℝ) (β : ℝ) (p : ℝ × (Fin (k+1) → ℝ)) (j : Fin (k+1)) :
    blockAdaptiveOverlap I a β p j ∈ Set.Icc (0:ℝ) 1 :=
  hierarchyMeanOverlap_bounds _ _ _ _ (fun i s => by cases s i <;> norm_num [spin]) _

theorem blockAdaptiveOverlap_monotone {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (a : Fin D → ℝ) (β : ℝ) (p : ℝ × (Fin (k+1) → ℝ)) :
    Monotone (blockAdaptiveOverlap I a β p) :=
  (hierarchyMeanOverlap_mono _ _ _ _ (fun i s => by cases s i <;> norm_num [spin])).comp
    (blockLevel_mono D N k)
end SK.Analytic

end
end

end

end OAI
