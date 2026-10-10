import OAI.Geometry.RuledCovering.Model

namespace OAI

noncomputable section
open Set

namespace RuledApproximation

def openParallelogramSet {E : Type*} [AddCommGroup E] [Module ℝ E]
    (c u v : E) : Set E :=
  {x | ∃ s ∈ Ioo (0 : ℝ) 1, ∃ t ∈ Ioo (0 : ℝ) 1,
    x = c + s • u + t • v}

def IsOpenParallelogram {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) : Prop :=
  ∃ c u v : E, LinearIndependent ℝ ![u, v] ∧ P = openParallelogramSet c u v

def Cylinder.openParallelogram (C : Cylinder) : Prop := IsOpenParallelogram C.base

def OpenParallelogramEnlargementStatement : Prop :=
  ∀ (n : ℕ) (C : Fin n → Cylinder), (∀ i, (C i).parallelogram) →
    ∀ ε : ℝ, 0 < ε →
      ∃ D : Fin n → Cylinder, (∀ i, (D i).axis = (C i).axis) ∧
        (∀ i, (D i).openParallelogram ∧ (D i).openBounded) ∧
        familySet C ⊆ familySet D ∧ familyArea D < familyArea C + ε

end RuledApproximation

end

end OAI
