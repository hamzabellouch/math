import OAI.Algebra.Finitistic.Bimodule.BimoduleShiftCoherence
import OAI.Algebra.Finitistic.Localization.NativeBoundedDerived
import Mathlib.CategoryTheory.Shift.Localization

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
section Finite
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]
variable [∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (p i))]

/-- The proved total-complex shift structure descends through the native derived localization. -/
instance derived_commShift : (derived k B P p hp).CommShift ℤ := by
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ))
      (functor k B P p hp ⋙ DerivedCategory.Q) (derived k B P p hp) :=
    ⟨derivedComparison k B P p hp⟩
  exact Functor.commShiftOfLocalization DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)) ℤ
    (functor k B P p hp ⋙ DerivedCategory.Q) (derived k B P p hp)
end Finite

namespace BoundedProjective
variable {k B} {P : BiComplex k B} (data : BoundedProjective k B P)
variable [HasDerivedCategory.{u+1} (ModuleCat.{u} B)]

instance commShift : data.derived.CommShift ℤ := by
  letI : ∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (data.degrees i)) :=
    fun i => data.projective (data.degrees i)
  exact BimoduleTotal.derived_commShift k B P data.degrees
    (intervalDegrees_strictMono data.lower data.upper)

/-- Full left B-valued derived tensor commutes with every integer shift. -/
def shiftComparison (s : ℤ) : shiftFunctor _ s ⋙ data.derived ≅ data.derived ⋙ shiftFunctor _ s :=
  data.derived.commShiftIso s
end BoundedProjective
end LittleFinitistic.BimoduleTotal

end

end OAI
