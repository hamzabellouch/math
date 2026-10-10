import Mathlib

namespace OAI

noncomputable section
open CategoryTheory

namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]

attribute [-instance] CompletePartialOrder.toSupSet in
def littleFinitisticDimension : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{u} A) (_ : Module.Finite A M) (_ : projectiveDimension M < ⊤),
    projectiveDimension M

def bigFinitisticDimension : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{u} A) (_ : projectiveDimension M < ⊤), projectiveDimension M

def InjectivesGenerate : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} A)
  ∀ (P : ObjectProperty (DerivedCategory (ModuleCat.{u} A))),
    P.IsClosedUnderIsomorphisms → P.IsTriangulated →
    (∀ I : Type u, P.IsClosedUnderColimitsOfShape (Discrete I)) →
    (∀ (M : ModuleCat.{u} A), Injective M →
      P ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) →
    ∀ X, P X

theorem extreme_left_right_asymmetry :
    ∃ (Λ : Type) (_ : Ring Λ) (_ : Algebra ℂ Λ),
      FiniteDimensional ℂ Λ ∧
      littleFinitisticDimension Λ = ⊤ ∧ bigFinitisticDimension Λ = ⊤ ∧
      littleFinitisticDimension Λᵐᵒᵖ = 0 ∧ bigFinitisticDimension Λᵐᵒᵖ = 0 ∧
      ¬ InjectivesGenerate Λ ∧ InjectivesGenerate Λᵐᵒᵖ := by
  sorry

end LittleFinitistic

end

end OAI
