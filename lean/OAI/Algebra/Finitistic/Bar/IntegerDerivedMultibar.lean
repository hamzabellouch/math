import OAI.Algebra.Finitistic.Bar.IndexedMultibarTotal
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
namespace DerivedBar
universe u
variable (D : Type u) [Ring D]

/-- Choose mathlib's constructed localization, rather than postulating a derived category. -/
local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)

/-- Nonnegative homological degree n is genuine integer cochain degree -n;
positive cochain degrees are extended by zero. -/
abbrev integerExtension : ChainComplex (ModuleCat.{u} D) ℕ ⥤
    CochainComplex (ModuleCat.{u} D) ℤ :=
  ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} D)

/-- The actual integer derived-category value of a nonnegative chain complex. -/
def integerQ : ChainComplex (ModuleCat.{u} D) ℕ ⥤ DerivedCategory (ModuleCat.{u} D) :=
  integerExtension D ⋙ DerivedCategory.Q

theorem integerQ_inverts : (chainQuasiIso D).IsInvertedBy (integerQ D) := by
  intro Z W f hf
  have : QuasiIso f := hf
  exact inferInstanceAs (IsIso (DerivedCategory.Q.map
    (HomologicalComplex.extendMap f ComplexShape.embeddingDownNat)))

/-- Comparison from the nonnegative-chain localization into the genuine integer
cochain derived category, obtained by its localization universal property. -/
def chainToIntegerDerived : chainDerived D ⥤ DerivedCategory (ModuleCat.{u} D) :=
  Localization.lift (integerQ D) (integerQ_inverts D) (chainQ D)

def chainToIntegerDerivedIso : chainQ D ⋙ chainToIntegerDerived D ≅ integerQ D :=
  Localization.fac (integerQ D) (integerQ_inverts D) (chainQ D)

/-- Exact homology-degree comparison for the integer construction. -/
def integerExtensionHomologyIso (Z : ChainComplex (ModuleCat.{u} D) ℕ) (n : ℕ) :
    ((integerExtension D).obj Z).homology (-(n : ℤ)) ≅ Z.homology n :=
  Z.extendHomologyIso ComplexShape.embeddingDownNat rfl

variable (k X : Type u) [Field k] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "Z" => (Functor.obj (ChainComplex.single₀ (ModuleCat D)) N)

/-- The constructed finite derived iterate, now viewed in the actual integer
cochain derived category, is represented by the exact indexed block complex.
This does not assert an extension of the tensor functor to arbitrary integer inputs. -/
def integerDerivedIterateIndexedIso (r : ℕ) :
    (chainToIntegerDerived D).obj
      ((derivedTensorIterate k D X r).obj ((chainQ D).obj Z)) ≅
    DerivedCategory.Q.obj
      ((integerExtension D).obj (RecursiveTotal.indexedMultibar k D X N r)) :=
  (chainToIntegerDerived D).mapIso (RecursiveTotal.derivedIterateIndexedIso k D X N r) ≪≫
    (chainToIntegerDerivedIso D).app (RecursiveTotal.indexedMultibar k D X N r)

/-- The entire leading-bar chain isomorphism survives in the integer derived category. -/
def integerIndexedLeadingIso (r : ℕ) :
    (integerQ D).obj (RecursiveTotal.indexedMultibar k D X N r) ≅
      (integerQ D).obj (barTotal k D (explicitMultibar k D X r Z)) :=
  (integerQ D).mapIso (RecursiveTotal.indexedLeadingIso k D X N r)
end DerivedBar

end

end OAI
