import OAI.Algebra.Finitistic.Bar.RecursiveSuffixInduction

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
local instance (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance recursiveSuffixTotalIndexDecidableEq (r n : ℕ) :
    DecidableEq (RecursiveTotal.Index r n) := Classical.decEq _
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local instance : Module A N := inflatedModule D X N
local instance : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

/-- The same canonical embedding on the actual recursive total, through the
previously proved finite-sum flattening. -/
def innerTotalEmbedding (r n : ℕ) :
    (RecursiveTotal.iter B Z r).X n →ₗ[k] term k A N (r+n) :=
  (innerEmbedding k D X N r n).comp
    ((RecursiveTotal.flattenIso B Z r n (𝟭 _)).hom.hom.restrictScalars k)

theorem innerTotalEmbedding_assemble (r n : ℕ) (v : RecursiveTotal.flat B Z r n) :
    innerTotalEmbedding k D X N r n ((RecursiveTotal.assemble B Z r n).hom v) =
      innerEmbedding k D X N r n v := by
  change innerEmbedding k D X N r n
    ((RecursiveTotal.flattenIso B Z r n (𝟭 _)).hom.hom
      ((RecursiveTotal.flattenIso B Z r n (𝟭 _)).inv.hom v)) = _
  have h := congrArg (fun f => f.hom v) (RecursiveTotal.flattenIso B Z r n (𝟭 _)).inv_hom_id
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h
  exact congrArg (innerEmbedding k D X N r n) h

theorem innerTotalEmbedding_differential (r n : ℕ)
    (v : (RecursiveTotal.iter B Z r).X (n+1)) :
    SquareZero.multibarAugmentedDifferential k D X N (r+n)
      (innerTotalEmbedding k D X N r (n+1) v) =
    -innerTotalEmbedding k D X N r n (((RecursiveTotal.iter B Z r).d (n+1) n).hom v) := by
  obtain ⟨w,rfl⟩ := (RecursiveTotal.flattenIso B Z r (n+1) (𝟭 _)).toLinearEquiv.symm.surjective v
  change SquareZero.multibarAugmentedDifferential k D X N (r+n)
    (innerTotalEmbedding k D X N r (n+1) ((RecursiveTotal.assemble B Z r (n+1)).hom w)) = _
  rw [innerTotalEmbedding_assemble, innerEmbedding_differential]
  have h := congrArg (fun f => f.hom w) (RecursiveTotal.differential_assemble B Z r n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  erw [← h, innerTotalEmbedding_assemble]

theorem innerTotalEmbedding_smul (r n : ℕ) (d : D)
    (v : (RecursiveTotal.iter B Z r).X n) :
    innerTotalEmbedding k D X N r n (d • v) =
      (inl d : A) • innerTotalEmbedding k D X N r n v := by
  change innerEmbedding k D X N r n
    ((RecursiveTotal.flattenIso B Z r n (𝟭 _)).hom.hom (d • v)) =
      (inl d : A) • innerEmbedding k D X N r n
        ((RecursiveTotal.flattenIso B Z r n (𝟭 _)).hom.hom v)
  rw [map_smul]
  exact innerEmbedding_smul k D X N r n d _

theorem innerTotalEmbedding_ideal_zero (r n : ℕ) (x : X)
    (v : (RecursiveTotal.iter B Z r).X n) :
    (inr x : A) • innerTotalEmbedding k D X N r n v = 0 :=
  innerEmbedding_ideal_zero k D X N r n x _

theorem innerTotalEmbedding_bottom (r : ℕ) (v : (RecursiveTotal.iter B Z (r+1)).X 0) :
    SquareZero.multibarAugmentedDifferential k D X N r
      (innerTotalEmbedding k D X N (r+1) 0 v) = 0 :=
  innerEmbedding_bottom k D X N r _

theorem innerTotalEmbedding_inclusion (r n : ℕ) (t : RecursiveTotal.Index r n)
    (v : RecursiveTotal.summand B Z r n t) :
    innerTotalEmbedding k D X N r n ((RecursiveTotal.inclusion B Z r n t).hom v) =
      innerEmbedding k D X N r n ((RecursiveTotal.lof B Z r n t).hom v) := by
  have h := congrArg (fun f => f.hom v) (RecursiveTotal.lof_assemble B Z r n t)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [← h, innerTotalEmbedding_assemble]

theorem innerTotalEmbedding_zero : innerTotalEmbedding k D X N 0 0 = LinearMap.id := by
  ext v
  have h := innerTotalEmbedding_inclusion k D X N 0 0 () v
  change innerTotalEmbedding k D X N 0 0 v = _ at h
  have he := congrArg (fun f => f v) (innerEmbedding_zero_lof k D X N ())
  exact h.trans he

theorem innerTotalEmbedding_zero_succ (n : ℕ) : innerTotalEmbedding k D X N 0 (n+1) = 0 := by
  unfold innerTotalEmbedding
  simp only [innerEmbedding, LinearMap.zero_comp]
end DerivedBar.ParityBridge

end

end OAI
