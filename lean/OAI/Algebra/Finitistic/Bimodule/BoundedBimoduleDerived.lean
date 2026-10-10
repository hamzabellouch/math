import OAI.Algebra.Finitistic.Bimodule.BimoduleSingleEvaluation
import OAI.Algebra.Finitistic.Rectification.InducedDerivedFunctor

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

/-- Exactly the bounded-right-projective data needed to compute tensor on every complex. -/
structure BoundedProjective (P : BiComplex k B) where
  lower : ℤ
  upper : ℤ
  bounded : ∀ n, n < lower ∨ upper < n → IsZero (P.X n)
  projective : ∀ n, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) n)

namespace BoundedProjective
variable {k B} {P : BiComplex k B} (data : BoundedProjective k B P)

abbrev degrees := intervalDegrees data.lower data.upper

theorem complete (n : ℤ) (hn : ∀ i, data.degrees i ≠ n) : IsZero (P.X n) :=
  outside_interval_isZero k B P data.lower data.upper data.bounded n hn

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]

/-- The native derived tensor endofunctor of this one fixed bounded projective bimodule complex. -/
def derived : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B) := by
  letI : ∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (data.degrees i)) :=
    fun i => data.projective (data.degrees i)
  exact BimoduleTotal.derived k B P data.degrees (intervalDegrees_strictMono data.lower data.upper)

instance additive : data.derived.Additive := by
  let : ∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (data.degrees i)) :=
    fun i => data.projective (data.degrees i)
  exact BimoduleTotal.derived_additive k B P data.degrees (intervalDegrees_strictMono data.lower data.upper)

def comparison : DerivedCategory.Q ⋙ data.derived ≅
    BimoduleTotal.functor k B P data.degrees (intervalDegrees_strictMono data.lower data.upper) ⋙ DerivedCategory.Q := by
  letI : ∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (data.degrees i)) :=
    fun i => data.projective (data.degrees i)
  exact derivedComparison k B P data.degrees (intervalDegrees_strictMono data.lower data.upper)

/-- Agreement with the canonical native degree-zero evaluation, including its full B action. -/
def singleEvaluation (N : ModuleCat.{u} B) :
    data.derived.obj (DerivedCategory.Q.obj (singleInput B N)) ≅
      DerivedCategory.Q.obj (moduleEvaluation k B P N) := by
  letI : ∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (data.degrees i)) :=
    fun i => data.projective (data.degrees i)
  exact derivedSingleEvaluation k B P N data.degrees
    (intervalDegrees_strictMono data.lower data.upper) data.complete
end BoundedProjective
end LittleFinitistic.BimoduleTotal

end

end OAI
