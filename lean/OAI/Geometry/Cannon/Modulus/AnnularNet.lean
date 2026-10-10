import Mathlib
import OAI.Geometry.Cannon.Boundary.PolynomialPacking

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
section
section
open Set Metric
open scoped NNReal ENNReal

namespace CannonNode

open Set Metric

theorem annular_net {X : Type*} [MetricSpace X] [CompactSpace X]
    (x : X) (A B R r : ℝ) (hr : 0 < r) :
    ∃ T : Finset X,
      (∀ y ∈ T, (A-1)*R ≤ dist y x ∧ dist y x ≤ (B+1)*R) ∧
      (∀ y ∈ T, ∀ z ∈ T, y ≠ z → r ≤ dist y z) ∧
      (∀ v, (A-1)*R ≤ dist v x → dist v x ≤ (B+1)*R →
        ∃ y ∈ T, dist v y ≤ r) := by
  let W := {v : X | (A-1)*R ≤ dist v x ∧ dist v x ≤ (B+1)*R}
  obtain ⟨T,hT,hsep,hcover⟩ := CannonNet.exists_finite_separated_net W
    (isCompact_univ.totallyBounded.subset (subset_univ W)) r hr
  exact ⟨T,fun y hy => hT hy,hsep,fun v hl hu => hcover v ⟨hl,hu⟩⟩

end CannonNode

end

end
end
end
end
end
end
end
end
end
end
end

end OAI
