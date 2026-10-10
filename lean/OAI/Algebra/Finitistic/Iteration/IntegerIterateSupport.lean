import OAI.Algebra.Finitistic.Bar.IntegerDerivedMultibar
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.Embedding.CochainComplex

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace DerivedBar.IterateSupport
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)
variable (N : ModuleCat.{u} D)

/-- The already constructed genuine derived iterate, viewed in integer degrees. -/
abbrev object (r : ℕ) := (chainToIntegerDerived D).obj
  ((derivedTensorIterate k D X r).obj
    ((chainQ D).obj ((ChainComplex.single₀ (ModuleCat D)).obj N)))

/-- Every actual iterate is cohomologically nonpositive. This uses the proved
integer comparison and its actual nonnegative chain representative. -/
instance isLE_zero (r : ℕ) : (object k D X N r).IsLE 0 := by
  let Z := RecursiveTotal.indexedMultibar k D X N r
  have : ((integerExtension D).obj Z).IsStrictlyLE 0 :=
    inferInstanceAs (CochainComplex.IsStrictlyLE (Z.extend ComplexShape.embeddingDownNat) 0)
  have : (DerivedCategory.Q.obj ((integerExtension D).obj Z)).IsLE 0 := inferInstance
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (integerDerivedIterateIndexedIso D k X N r).symm 0

theorem positive_homology_zero (r : ℕ) (i : ℤ) (hi : 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) i).obj (object k D X N r)) :=
  DerivedCategory.isZero_of_isLE _ 0 i hi

/-- Nonzero actual iterates have a nonzero cohomology group in nonpositive degree. -/
theorem nonzero_homology (r : ℕ) (h : ¬ IsZero (object k D X N r)) :
    ∃ n : ℕ, ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).obj
      (object k D X N r)) := by
  by_contra hn
  push Not at hn
  have hz (i : ℤ) : IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) i).obj
      (object k D X N r)) := by
    by_cases hi : i ≤ 0
    · obtain ⟨n,rfl⟩ := Int.exists_eq_neg_ofNat hi
      exact hn n
    · exact positive_homology_zero k D X N r i (by omega)
  have : (object k D X N r).IsLE (-1) :=
    (DerivedCategory.isLE_iff _ _).mpr (fun i _ => hz i)
  have : (object k D X N r).IsGE 0 :=
    (DerivedCategory.isGE_iff _ _).mpr (fun i _ => hz i)
  apply h
  apply (IsZero.iff_id_eq_zero _).mpr
  exact DerivedCategory.TStructure.t.zero (𝟙 _) (-1) 0 (by omega)
end DerivedBar.IterateSupport

end

end OAI
