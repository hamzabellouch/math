import Mathlib
import OAI.Probability.Subsphere.Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereCurrent

namespace KernelLearner

/-- Borel probabilities, including counterfactual states. -/
def BorelRules {d M T : ℕ} (L : KernelLearner d M T) : Prop :=
  ∀ t q dest, Measurable (fun obs => L.transition t q obs dest)

end KernelLearner

namespace SeededLearner

end SeededLearner

end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v
namespace SubsphereCurrent.Affine

end SubsphereCurrent.Affine
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe v
namespace SubsphereCurrent.Weighted

def RadiusWeightedEstimate : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    (∀ W : ℝ, 1 ≤ W → ∀ (V : Type v) [Fintype V] [Nonempty V],
      (Fintype.card V : ℝ) ≤ W →
      ∀ κ : V → Observation d (d/16) → ℝ≥0∞,
      (∀ v, Measurable (κ v)) → (∀ obs, ∑ v, κ v obs ≤ 1) →
      ∀ g : V → Sphere d → ℝ≥0∞,
      (∀ v, Measurable (g v)) → (∀ v s, g v s ≤ 1) →
      ∀ n : ℕ, (d : ℝ)/2 ≤ n → n ≤ d →
      norm d n (blockInput κ g) ≤
        (ENNReal.ofReal W)^(1/((d/16 : ℕ) : ℝ))*ENNReal.ofReal (C^d)*(⨆ v, norm d (n-2) (g v))) ∧
    (∀ n : ℕ, (d : ℝ)/2 ≤ n → n ≤ d →
      ∀ π : Measure (Sphere d), IsProbabilityMeasure π →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
      norm d n (terminalInput π ε) ≤ ENNReal.ofReal (C^d)*(ENNReal.ofReal ε)^((d : ℝ)/16))

end SubsphereCurrent.Weighted
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe v
namespace SubsphereCurrent.Weighted

end SubsphereCurrent.Weighted
end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereCurrent

end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v
namespace SubsphereCurrent
namespace Fixed

namespace Stream
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [MeasurableSpace J] [Fintype J] [MeasurableSingletonClass J]
  {T : ℕ}

end Stream

end Fixed
end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v
namespace SubsphereCurrent.Affine

end SubsphereCurrent.Affine
end
end

end OAI
