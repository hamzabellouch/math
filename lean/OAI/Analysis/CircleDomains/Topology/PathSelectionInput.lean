import OAI.Analysis.CircleDomains.Uniformization.Conformal
import OAI.Analysis.CircleDomains.Probability.PathHitLaws
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! Published input for the compact-arc reduction: Kechris, Classical
Descriptive Set Theory (1995), Theorem 18.1, p.120, and Theorem 29.9,
p.227. We use only Borel relations between sphere path spaces with all
sections nonempty, and measurability after completing one probability law. -/

open Set MeasureTheory
open scoped Topology

namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

def BorelPathRelationSelection : Prop :=
  ∀ (μ : ProbabilityMeasure C(PathTime, Sphere))
    (R : Set (C(PathTime, Sphere) × C(PathTime, Sphere))),
    MeasurableSet R → (∀ γ, ∃ α, (γ, α) ∈ R) →
    ∃ f : C(PathTime, Sphere) → C(PathTime, Sphere),
      NullMeasurable f (μ : Measure C(PathTime, Sphere)) ∧ ∀ γ, (γ, f γ) ∈ R

end CircleDomainRigidity

end OAI
