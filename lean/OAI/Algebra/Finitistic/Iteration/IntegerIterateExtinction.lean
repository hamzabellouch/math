import OAI.Algebra.Finitistic.Iteration.IntegerIterateAmplitude
import OAI.Algebra.Finitistic.Bar.BarAdditive

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex ZeroObject
namespace DerivedBar.IterateSupport
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance integerIterateExtinctionHasDerivedCategory : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)

/-- The integer derived object of an actual nonnegative chain complex vanishes
exactly when the original chain complex is exact in every degree. -/
theorem integerQ_isZero_iff (Z : ChainComplex (ModuleCat.{u} D) ℕ) :
    IsZero ((integerQ D).obj Z) ↔ ∀ n, Z.ExactAt n := by
  constructor
  · intro h n
    apply (exactAt_iff_isZero_homology _ _).mpr
    have hz := (DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).map_isZero h
    exact ((DerivedCategory.homologyFunctorFactors (ModuleCat D) (-(n : ℤ))).app
      ((integerExtension D).obj Z) ≪≫ integerExtensionHomologyIso D Z n).isZero_iff.mp hz
  · intro h
    have : ((integerExtension D).obj Z).IsStrictlyLE 0 := by
      exact inferInstanceAs (CochainComplex.IsStrictlyLE
        (Z.extend ComplexShape.embeddingDownNat) 0)
    have : ((integerQ D).obj Z).IsLE 0 := by
      change (DerivedCategory.Q.obj ((integerExtension D).obj Z)).IsLE 0
      infer_instance
    have hz (i : ℤ) : IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) i).obj
        ((integerQ D).obj Z)) := by
      by_cases hi : i ≤ 0
      · obtain ⟨n,rfl⟩ := Int.exists_eq_neg_ofNat hi
        exact ((DerivedCategory.homologyFunctorFactors (ModuleCat D) (-(n : ℤ))).app
          ((integerExtension D).obj Z) ≪≫ integerExtensionHomologyIso D Z n).isZero_iff.mpr
            ((exactAt_iff_isZero_homology _ _).mp (h n))
      · exact DerivedCategory.isZero_of_isLE _ 0 i (by omega)
    have : ((integerQ D).obj Z).IsLE (-1) :=
      (DerivedCategory.isLE_iff _ _).mpr (fun i _ => hz i)
    have : ((integerQ D).obj Z).IsGE 0 :=
      (DerivedCategory.isGE_iff _ _).mpr (fun i _ => hz i)
    apply (IsZero.iff_id_eq_zero _).mpr
    exact DerivedCategory.TStructure.t.zero (𝟙 _) (-1) 0 (by omega)

local instance : (barTotalFunctor k D).PreservesZeroMorphisms where
  map_zero Z W := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply HomologicalComplex₂.total.hom_ext (K := barBicomplex k D Z)
    intro i q h
    erw [ι_barTotalFunctor_map k D (0 : Z ⟶ W) i q n h]
    simp [termMap_zero]
    erw [zero_comp,comp_zero]
    rfl
local instance : (tensorTotalFunctor k D X).PreservesZeroMorphisms := by
  dsimp [tensorTotalFunctor]
  infer_instance

omit [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X]
/-- The actual resolve-and-tensor functor sends an acyclic chain input to an acyclic output. -/
theorem tensor_acyclic (Z : ChainComplex (ModuleCat.{u} D) ℕ)
    (h : ∀ n, Z.ExactAt n) : ∀ n, ((tensorTotalFunctor k D X).obj Z).ExactAt n := by
  let f : Z ⟶ 0 := 0
  have : QuasiIso f := ⟨fun n => (quasiIsoAt_iff_exactAt f n (h n)).mpr
    ((exactAt_iff_isZero_homology _ _).mpr
      ((HomologicalComplex.homologyFunctor _ (.down ℕ) n).map_isZero (Limits.isZero_zero _)))⟩
  let G := tensorTotalFunctor k D X
  have hz := G.map_isZero (Limits.isZero_zero (ChainComplex (ModuleCat.{u} D) ℕ))
  intro n
  apply (exactAt_iff_of_quasiIsoAt (G.map f) n).mpr
  exact (exactAt_iff_isZero_homology _ _).mpr
    ((HomologicalComplex.homologyFunctor _ (.down ℕ) n).map_isZero hz)

variable (N : ModuleCat.{u} D)

/-- Extinction is permanent for the genuine bar-derived iteration. -/
theorem zero_succ (r : ℕ) (h : IsZero (object k D X N r)) :
    IsZero (object k D X N (r+1)) := by
  apply (resolvedModelIso k D X N (r+1)).isZero_iff.mpr
  apply (integerQ_isZero_iff (D := D) (resolvedModel k D X N (r+1))).mpr
  apply tensor_acyclic k D X (resolvedModel k D X N r)
  exact (integerQ_isZero_iff (D := D) (resolvedModel k D X N r)).mp
    ((resolvedModelIso k D X N r).isZero_iff.mp h)

/-- A proved zero iterate kills every later iterate, without a native-functor comparison premise. -/
theorem zero_of_le (t r : ℕ) (htr : t ≤ r) (h : IsZero (object k D X N t)) :
    IsZero (object k D X N r) := by
  induction r, htr using Nat.le_induction with
  | base => exact h
  | succ r _ ih => exact zero_succ k D X N r ih
end DerivedBar.IterateSupport

end

end OAI
