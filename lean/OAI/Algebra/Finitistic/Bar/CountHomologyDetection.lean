import OAI.Algebra.Finitistic.Bar.CountRetracts
import OAI.Algebra.Finitistic.Bar.DirectSumExactness
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex TrivSqZeroExt
noncomputable section
namespace DerivedBar
universe u v w z

theorem nonzero_of_functor_retract {C : Type u} [Category.{v} C]
    {E : Type w} [Category.{z} E] [HasZeroMorphisms E]
    (F : C ⥤ E) {V W : C} (i : V ⟶ W) (p : W ⟶ V) (hip : i ≫ p = 𝟙 V)
    (h : ¬ IsZero (F.obj V)) : ¬ IsZero (F.obj W) := by
  intro hz
  apply h
  rw [IsZero.iff_id_eq_zero]
  have hm := congrArg F.map hip
  rw [F.map_comp, F.map_id] at hm
  rw [← hm, hz.eq_of_tgt (F.map i) 0, zero_comp]

variable (D : Type u) [Ring D]
local instance countHomologyDetectionHasDerivedCategory :
    HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)

/-- Exact comparison of integer derived homology and the original chain degree. -/
def integerQHomologyIso (K : ChainComplex (ModuleCat.{u} D) ℕ) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} D) (-(n:ℤ))).obj ((integerQ D).obj K) ≅
      K.homology n :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} D) (-(n:ℤ))).app
    ((integerExtension D).obj K) ≪≫ integerExtensionHomologyIso D K n
end DerivedBar
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance (V : ModuleCat D) : Module k V := BimoduleTensor.scalarModule k D V
local instance (V : ModuleCat D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
variable (N : ModuleCat D)
local notation "A" => TrivSqZeroExt D X
local instance : Module A N := inflatedModule D X N
local instance : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)
local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)
local notation "S" => SquareZero.twoSidedWeightComplex k D X N (inflated_ideal_zero D X N)
local notation "T" => tensorBarComplex k A D N (fstHom k D X)

/-- Uniform vanishing of the original count homologies implies vanishing of
the entire actual balanced tensor bar, including its infinite count family. -/
theorem tensorBar_homology_zero_of_counts (n : ℕ) (h : ∀ r, IsZero ((S r).homology n)) :
    IsZero ((T).homology n) :=
  (directSumComplex_homology_zero D S n h).of_iso
    ((HomologicalComplex.homologyFunctor (ModuleCat D) (.down ℕ) n).mapIso
      (SquareZero.tensorCountSplitting k D X N (inflated_ideal_zero D X N)))

theorem tensorBar_homology_nonzero_of_count (r n : ℕ) (h : ¬ IsZero ((S r).homology n)) :
    ¬ IsZero ((T).homology n) :=
  nonzero_of_functor_retract (HomologicalComplex.homologyFunctor (ModuleCat D) (.down ℕ) n)
    (countTensorBarInclusion k D X N r) (countTensorBarProjection k D X N r)
      (countTensorBar_retract k D X N r) h

/-- Direct input bridge for uniform bounds on the original count objects in
the integer derived category, yielding actual base-change Tor vanishing. -/
theorem baseChangeTor_zero_of_counts (n : ℕ)
    (h : ∀ r, IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n:ℤ))).obj
      ((integerQ D).obj (S r)))) :
    IsZero (((Balanced.tensorFunctor (fstHom k D X)).leftDerived n).obj (ModuleCat.of A N)) :=
  (tensorBar_homology_zero_of_counts k D X N n
    (fun r => (h r).of_iso (integerQHomologyIso D (S r) n).symm)).of_iso
      (Balanced.tensorBarHomologyIso (fstHom k D X) N n)

/-- A surviving original count homology is a nonzero actual Tor group. -/
theorem baseChangeTor_nonzero_of_count (r n : ℕ)
    (h : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n:ℤ))).obj
      ((integerQ D).obj (S r)))) :
    ¬ IsZero (((Balanced.tensorFunctor (fstHom k D X)).leftDerived n).obj (ModuleCat.of A N)) := by
  intro hz
  have hc : IsZero ((S r).homology n) → False := by
    intro hc
    exact h (hc.of_iso (integerQHomologyIso D (S r) n))
  apply tensorBar_homology_nonzero_of_count k D X N r n hc
  exact hz.of_iso (Balanced.tensorBarHomologyIso (fstHom k D X) N n).symm
end DerivedBar.ParityBridge

end

end OAI
