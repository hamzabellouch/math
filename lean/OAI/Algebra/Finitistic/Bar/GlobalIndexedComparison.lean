import OAI.Algebra.Finitistic.Bar.IndexedAssemblyComparison
import OAI.Algebra.Finitistic.Bar.SignedBlockExplicit

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
local instance (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance globalIndexedComparisonIndexDecidableEq (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local notation "c" => ComplexShape.down ℕ
local instance : Module A N := inflatedModule D X N
local instance : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

@[reassoc] theorem eqToHom_chain_d {Y W : ChainComplex (ModuleCat.{u} D) ℕ}
    (h : Y=W) (i j : ℕ) :
    Y.d i j ≫ eqToHom (congrArg (fun T => T.X j) h) =
      eqToHom (congrArg (fun T => T.X i) h) ≫ W.d i j := by
  subst W
  simp

/-- The full leading comparison transferred through the actual flattening. -/
theorem flatEmbedding_differential (r n : ℕ) :
    flatEmbedding k D X N r (n+1) ≫
      ModuleCat.ofHom (SquareZero.multibarTwoSidedDifferential k D X N (r+n)) =
    RecursiveTotal.differential (leadingBarSequence k D X r) Z (r+1) n ≫ flatEmbedding k D X N r n := by
  simp only [flatEmbedding, Category.assoc, leadingTotalEmbedding_differential]
  rw [← eqToHom_chain_d_assoc (h := leadingIter_total k D X N r)]
  rw [← Category.assoc, ← differential_assemble, Category.assoc]

private theorem conjugated_differential_comp {C : Type*} [Category C]
    {S₁ S₀ T₁ T₀ V₁ V₀ : C} (a : T₁ ⟶ S₁) (b : S₀ ⟶ T₀)
    (d : S₁ ⟶ S₀) (δ : V₁ ⟶ V₀) (s₁ : T₁ ⟶ V₁) (s₀ : T₀ ⟶ V₀)
    (f₁ : S₁ ⟶ V₁) (f₀ : S₀ ⟶ V₀)
    (h₀ : f₀ = b ≫ s₀) (h₁ : a ≫ f₁ = s₁) (hd : f₁ ≫ δ = d ≫ f₀) :
    (a ≫ d ≫ b) ≫ s₀ = s₁ ≫ δ := by
  rw [Category.assoc, Category.assoc, ← h₀, ← hd, ← Category.assoc, h₁]

/-- The original Shape differential intertwines the independently defined literal
parity faces through the original tensor-block assembly. -/
theorem indexedDifferential_assembly (r n : ℕ) :
    indexedDifferential k D X N r n ≫ shapeAssembly k D X N r n =
      shapeAssembly k D X N r (n+1) ≫
        ModuleCat.ofHom (SquareZero.multibarTwoSidedDifferential k D X N (r+n)) := by
  simp only [indexedDifferential, flatLeadingMultibar, flatComplex, ChainComplex.of_d]
  exact conjugated_differential_comp _ _ _ _ _ _ _ _
    (flatEmbedding_coordinates k D X N r n)
    (moduleFlatCoordinates_inv_flatEmbedding k D X N r (n+1))
    (flatEmbedding_differential k D X N r n)

theorem inflated_ideal_zero (x : X) (v : N) : (inr x : A) • v=0 := by
  change (0:D) • v=0
  exact zero_smul D v

/-- The global comparison identifies the independently defined recursive differential,
Shape coordinates, signed block differential, and both sign identities. -/
theorem globalIndexedComparison (r n : ℕ) :
    (indexedDifferential k D X N r n).hom =
      (-1:k)^r • Multibar.Indexed.blockDifferential k D X N
        (fun x v => inflated_ideal_zero D X N x v) (r+n) r := by
  apply LinearMap.ext
  intro v
  apply shapeAssembly_injective k D X N r n
  have hd := congrArg (fun f => f.hom v) (indexedDifferential_assembly k D X N r n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at hd
  rw [hd]
  rw [Multibar.Indexed.blockDifferential_eq_explicit]
  change SquareZero.multibarTwoSidedDifferential k D X N (r+n)
      (Multibar.Indexed.decomposition k D X N (r+(n+1)) r v).val =
    (Multibar.Indexed.decomposition k D X N (r+n) r
      ((-1:k)^r • ((Multibar.Indexed.decomposition k D X N (r+n) r).symm
        ((-1:k)^r • SquareZero.multibarCountDifferential k D X N
          (fun x v => inflated_ideal_zero D X N x v) (r+n) r
          (Multibar.Indexed.decomposition k D X N (r+(n+1)) r v))))).val
  have hs := ((Multibar.Indexed.decomposition k D X N (r+n) r).toLinearMap.restrictScalars k).map_smul
    ((-1:k)^r) ((Multibar.Indexed.decomposition k D X N (r+n) r).symm
        ((-1:k)^r • SquareZero.multibarCountDifferential k D X N
          (fun x v => inflated_ideal_zero D X N x v) (r+n) r
          (Multibar.Indexed.decomposition k D X N (r+(n+1)) r v)))
  change Multibar.Indexed.decomposition k D X N (r+n) r (_ • _) =
    _ • Multibar.Indexed.decomposition k D X N (r+n) r _ at hs
  rw [hs, LinearEquiv.apply_symm_apply, smul_smul, ← mul_pow]
  simp only [neg_one_mul, neg_neg, one_pow, one_smul]
  rfl
end DerivedBar.ParityBridge

end

end OAI
