import OAI.Analysis.CircleDomains.Modulus.ReversedPhysicalLength
import OAI.Analysis.CircleDomains.Topology.BasePathCodes

namespace OAI

/-! Reversal stability of allowed paths, including the physical metric,
both incidence families, retained tuples, and residual-image nullity. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem allowedTaggedPath_reversed (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (Γ : TaggedPath X) (hΓ : AllowedTaggedPath d ν N Γ)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    AllowedTaggedPath d ν N (reversedTaggedPath Γ) := by
  refine ⟨?_, tagRules_reversed d.levels N Γ hΓ.2.1, ?_, ?_, ?_⟩
  · change physicalDomainLength d.domainEquiv d.basePoint (reversedPath Γ.1) < ∞
    rw [physicalDomainLength_reversed]
    exact hΓ.1
  · apply residualConstraintFamily_reversed d.dust (fun _ => pathHitSet)
      d.priorDeletions d.priorLaws (fun i => priorHitMass (d.priorLaws i)) Γ hΓ.2.2.1
    intro i x
    exact le_rfl
  · exact residualConstraintFamily_reversed d.dust d.levels (fun _ => d.flagDeletions)
      (fun _ => volume) d.levelWeights Γ hΓ.2.2.2.1 hpoint
  · rw [residualImage_reversed]
    exact hΓ.2.2.2.2

end CircleDomainRigidity

end

end OAI
