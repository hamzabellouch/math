import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Model

namespace OAI

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme.{0}}
abbrev complexSectionModule (f : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) :
    Module ℂ (GlobalSections X M) :=
  Module.compHom _ (baseScalars f)

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
def EventualSeshadriEquality (S : Surface) (L : LineBundle S.scheme) : Prop :=
  ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
    ∃ Z : ℕ → Set (Configuration S r),
      (∀ n, IsClosed (Z n) ∧ Z n ≠ Set.univ) ∧
      (∃ p : Configuration S r, ∀ n, p ∉ Z n) ∧
      ∀ p : Configuration S r, (∀ n, p ∉ Z n) →
        seshadriConstant S L r p = Real.sqrt ((selfIntersection S L : ℝ) / r)

end
end MaximalSeshadri.Geometry

end OAI
