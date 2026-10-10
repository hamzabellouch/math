import OAI.Analysis.CircleDomains.Selection.AffinePhysicalRestriction
import OAI.Analysis.CircleDomains.Selection.AffineResidualBounds
import OAI.Analysis.CircleDomains.Probability.AffineResidualNull

namespace OAI

/-! The actual affine restriction of an allowed tagged path is allowed.
The only level hypothesis is the pointwise incidence bound already required
of the level weights. No path-stability statement is assumed. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace C(PathTime, X)]

theorem allowedTaggedPath_affine (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (Γ : TaggedPath X) (hΓ : AllowedTaggedPath d ν N Γ)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    {a b : PathTime} (hab : a < b) :
    AllowedTaggedPath d ν N (affineRestrictedTaggedPath a b Γ) := by
  refine ⟨physicalDomainLength_affine_finite d.domainEquiv hU d.basePoint
    ⟨Γ.1, hΓ.1⟩ hab, tagRules_affineRestricted d.levels N hab Γ hΓ.2.1, ?_, ?_, ?_⟩
  · apply residualConstraintFamily_affine d.dust (fun _ => pathHitSet) d.priorDeletions
      d.priorLaws (fun i => priorHitMass (d.priorLaws i)) Γ hΓ.2.2.1 _ hab
    intro i x
    exact le_rfl
  · exact residualConstraintFamily_affine d.dust d.levels (fun _ => d.flagDeletions)
      (fun _ => volume) d.levelWeights Γ hΓ.2.2.2.1 hpoint hab
  · exact residualImage_affine_null d.dust hab Γ ν hΓ.2.2.2.2

end CircleDomainRigidity

end

end OAI
