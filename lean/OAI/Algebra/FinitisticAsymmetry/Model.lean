import Mathlib
import OAI.Algebra.Finitistic.Basic

namespace OAI

noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]

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

end LittleFinitistic
end

end OAI
