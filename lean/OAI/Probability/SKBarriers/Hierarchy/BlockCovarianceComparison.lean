import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.WeightedBlockMass
import OAI.Probability.SKBarriers.Hierarchy.BlockObservable

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {S : Type} [Fintype S] [Nonempty S]

theorem blockObservable_compare {D N k : ℕ} (hN : 0<N)
    (H : Fin D → S → ℝ) (F : Fin (k+1) → Fin N → S → ℝ) (c : S → ℝ)
    (w : Fin (k+1) → ℝ) (hw : ∀ b, 0≤w b) (hs : ∑ b, w b=1)
    (A : ℝ) (C : Fin (k+1) → ℝ)
    (hdiag : ∀ s, (1/2:ℝ)*(∑ i, (H i s)^2)-(1/2:ℝ)*(∑ b, ∑ i, (F b i s)^2) ≤ A)
    (hkernel : ∀ b s t, -C b ≤ (1/2:ℝ)*(∑ i, H i s*H i t)-
      (1/2:ℝ)*(∑ a, if a≤b then ∑ i, F a i s*F a i t else 0)) :
    hierarchyPressure (blockDimension D N k) (weightedBlockMass D N k w)
      (affineLogPartition c (observableExponent (blockDimension D N k) (blockObservable H F)
        (interpolationCoefficient (blockDimension D N k) (blockInterpolationChoice D N k) 1))) 0 ≤
    hierarchyPressure (blockDimension D N k) (weightedBlockMass D N k w)
      (affineLogPartition c (observableExponent (blockDimension D N k) (blockObservable H F)
        (interpolationCoefficient (blockDimension D N k) (blockInterpolationChoice D N k) 0))) 0+
      A+∑ b, w b*C b := by
  have hm := weightedBlockMass_valid D N k w hw hs
  have HH := observablePressure_covariance_comparison (blockDimension D N k) (blockObservable H F) c
    (weightedBlockMass D N k w) (blockInterpolationChoice D N k) hm.1 hm.2 A (weightedBlockAtom D N k C)
    (fun s => by simpa only [pow_two,blockObservable_covariance] using hdiag s)
    (fun j hj s t => by
      rw [hierarchyAtom_weightedBlockMass D N k w hs] at hj
      obtain ⟨b,rfl⟩ := weightedBlockAtom_ne_zero D N k w j hj
      rw [weightedBlockAtom_at D N k C hN,blockObservable_partial_covariance]
      exact hkernel b s t)
  simp_rw [hierarchyAtom_weightedBlockMass D N k w hs] at HH
  rw [weightedBlockAtom_sum_mul] at HH
  simpa only [weightedBlockAtom_at D N k C hN] using HH

end
end SK.Analytic

end
end

end OAI
