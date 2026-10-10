import Mathlib
import OAI.Geometry.Cannon.Flows.Oscillation

namespace OAI

section
section
section
noncomputable section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators

namespace CannonApprox

open Set Metric CannonCrossEnergy

def meshEnergy {X ι : Type*} [MetricSpace X] [Fintype ι]
    (p : ι → X) (r J : ℝ) (F : X → ℝ) (K : Set X) : ℝ := by
  classical
  exact ∑ i : {i : ι // (ball (p i) (2*r) ∩ K).Nonempty},
    (oscillation F (closedBall (p i.val) (J*r)))^2

lemma meshEnergy_nonneg {X ι : Type*} [MetricSpace X] [Fintype ι]
    (p : ι → X) (r J : ℝ) (F : X → ℝ) (K : Set X) :
    0 ≤ meshEnergy p r J F K := by
  classical
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end CannonApprox

end
end
end
end
end
end
end
end

end OAI
