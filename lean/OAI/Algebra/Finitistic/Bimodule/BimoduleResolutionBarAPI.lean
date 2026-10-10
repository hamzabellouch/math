import OAI.Algebra.Finitistic.Bimodule.BimoduleBarStalk

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} B) :=
  HasDerivedCategory.standard (ModuleCat.{u} B)
variable (P : BiComplex k B) (X : ModuleCat.{u} (Enveloping k B)) (length : ℕ)
variable (ε : P ⟶ bimoduleStalk k B X) (hε : QuasiIso ε)
variable (hproj : ∀ n, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) n))
variable (hbound : ∀ n, n < -(length : ℤ) ∨ 0 < n → IsZero (P.X n))

/-- Package exactly the ordinary worker's actual bounded bimodule resolution
API. Augmentation, quasi-isomorphism, projectivity and support are all explicit. -/
def ofNonpositiveResolution : AugmentedProjective k B P X where
  data := { lower := -(length : ℤ), upper := 0, bounded := hbound, projective := hproj }
  augmentation := ε
  quasiIso := hε

local notation "R" => ofNonpositiveResolution P X length ε hε hproj hbound

/-- Integration API for Q_X: the native integer-derived functor agrees naturally
with the genuine bar-derived functor after chainToIntegerDerived. -/
def nonpositiveResolutionBarIso :
    DerivedBar.chainToIntegerDerived B ⋙ (R).data.derived ≅
      DerivedBar.derivedTensor k B (barModule (X := X)) ⋙ DerivedBar.chainToIntegerDerived B :=
  nativeBarIso R (zeroDegreeIndex R (by dsimp [ofNonpositiveResolution]; omega) (by rfl))
    (zeroDegreeIndex_eq R (by dsimp [ofNonpositiveResolution]; omega) (by rfl))

/-- Exact source-style F^r applied to a native degree-zero module, represented
by the genuine Section 6 indexed multibar. All comparison data is constructed. -/
def nonpositiveResolutionPowerIso (N : ModuleCat.{u} B) (r : ℕ) :
    ((R).data.derived.obj^[r]) (DerivedCategory.Q.obj (singleInput B N)) ≅
      DerivedCategory.Q.obj ((DerivedBar.integerExtension B).obj
        (DerivedBar.RecursiveTotal.indexedMultibar k B (barModule (X := X)) N r)) :=
  (eqToIso (nativeIterate_obj R r _)).symm ≪≫
    nativeStalkIndexedIso R (by dsimp [ofNonpositiveResolution]; omega) (by rfl) N r
end LittleFinitistic.BimoduleTotal

end

end OAI
