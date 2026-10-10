import OAI.Algebra.Finitistic.Iteration.IntegerIterateSupport
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import OAI.Algebra.Finitistic.Bar.SignedBlockModel
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct DirectSum
namespace DerivedBar.IterateSupport
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)
local instance (N : ModuleCat.{u} D) : Module k N := BimoduleTensor.scalarModule k D N
local instance (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable [FiniteDimensional k D] [FiniteDimensional k X]
variable (N : ModuleCat.{u} D) [FiniteDimensional k N]

instance tensor_finite {n r : ℕ} (p : Multibar.Indexed.Shape n r) :
    FiniteDimensional k (Multibar.Indexed.tensor k D X N p) := by
  induction p with
  | nil => exact inferInstanceAs (FiniteDimensional k N)
  | base p ih =>
    let := ih
    exact inferInstanceAs (FiniteDimensional k (D ⊗[k] Multibar.Indexed.tensor k D X N p))
  | ideal p ih =>
    let := ih
    exact inferInstanceAs (FiniteDimensional k (X ⊗[k] Multibar.Indexed.tensor k D X N p))

instance indexed_finite (r n : ℕ) : FiniteDimensional k
    ((ModuleCat.restrictScalars (algebraMap k D)).obj
      ((RecursiveTotal.indexedMultibar k D X N r).X n)) := by
  let V := ⨁ p : Multibar.Indexed.Shape (r+n) r,
    Multibar.Indexed.outerTensor k D X N p
  have : Module.Finite k V := inferInstance
  have : Module.Finite D V := Module.Finite.of_restrictScalars_finite k D V
  have : Module.Finite D ((ModuleCat.restrictScalars (algebraMap k D)).obj
      ((RecursiveTotal.indexedMultibar k D X N r).X n)) :=
    inferInstanceAs (Module.Finite D V)
  have : IsScalarTower k D ((ModuleCat.restrictScalars (algebraMap k D)).obj
      ((RecursiveTotal.indexedMultibar k D X N r).X n)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact Module.Finite.trans D ((ModuleCat.restrictScalars (algebraMap k D)).obj
    ((RecursiveTotal.indexedMultibar k D X N r).X n))

omit [FiniteDimensional k D] in
/-- Homology is a quotient of a subspace of the term in that degree. -/
theorem homology_finite {ι : Type*} (c : ComplexShape ι)
    (Z : HomologicalComplex (ModuleCat.{u} D) c) (i : ι)
    [FiniteDimensional k ((ModuleCat.restrictScalars (algebraMap k D)).obj (Z.X i))] :
    FiniteDimensional k ((ModuleCat.restrictScalars (algebraMap k D)).obj (Z.homology i)) := by
  let F := ModuleCat.restrictScalars (algebraMap k D)
  have : FiniteDimensional k (F.obj (Z.sc i).X₂) :=
    inferInstanceAs (FiniteDimensional k ((ModuleCat.restrictScalars (algebraMap k D)).obj (Z.X i)))
  have : FiniteDimensional k (F.obj (Z.sc i).cycles) :=
    FiniteDimensional.of_injective (F.map (Z.sc i).iCycles).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact FiniteDimensional.of_surjective (F.map (Z.sc i).homologyπ).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- Actual cohomology of every derived iterate is finite-dimensional in every degree. -/
theorem cohomology_finite (r : ℕ) (i : ℤ) : FiniteDimensional k
    ((ModuleCat.restrictScalars (algebraMap k D)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat D) i).obj (object k D X N r))) := by
  let F := ModuleCat.restrictScalars (algebraMap k D)
  by_cases hi : i ≤ 0
  · obtain ⟨n,rfl⟩ := Int.exists_eq_neg_ofNat hi
    let Z := RecursiveTotal.indexedMultibar k D X N r
    let e := (DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).mapIso
      (integerDerivedIterateIndexedIso D k X N r) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat D) (-(n : ℤ))).app
        ((integerExtension D).obj Z) ≪≫ integerExtensionHomologyIso D Z n
    have : FiniteDimensional k (F.obj (Z.homology n)) :=
      homology_finite k D (.down ℕ) Z n
    exact FiniteDimensional.of_injective (F.map e.hom).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  · have hz := Functor.map_isZero F (positive_homology_zero k D X N r i (by omega))
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    infer_instance
end DerivedBar.IterateSupport

end

end OAI
