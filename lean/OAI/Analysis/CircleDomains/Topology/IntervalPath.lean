import OAI.Analysis.CircleDomains.Probability.AffinePhysicalTimeMeasure

namespace OAI

open Set

noncomputable section
namespace CircleDomainRigidity

def intervalPath {X : Type*} [MetricSpace X] (γ : C(PathTime, X)) (a b : PathTime) :
    Path (γ a) (γ b) where
  toContinuousMap := affineRestrictedPath a b γ
  source' := by
    have h0 : (0 : PathTime) = ⊥ := Subtype.ext rfl
    change γ (affinePathTime a b 0) = γ a
    rw [h0, affinePathTime_zero]
  target' := by
    have h1 : (1 : PathTime) = ⊤ := Subtype.ext rfl
    change γ (affinePathTime a b 1) = γ b
    rw [h1, affinePathTime_one]

theorem intervalPath_range {X : Type*} [MetricSpace X] (γ : C(PathTime, X))
    {a b : PathTime} (hab : a < b) :
    range (intervalPath γ a b) = γ '' Icc a b := by
  change range (γ ∘ affinePathTime a b) = _
  rw [range_comp, range_affinePathTime hab]

end CircleDomainRigidity

end

end OAI
