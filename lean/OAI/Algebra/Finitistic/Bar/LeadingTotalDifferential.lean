import OAI.Algebra.Finitistic.Bar.LeadingTotalEmbedding

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive TensorProduct TrivSqZeroExt
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
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "DB" => barFunctor k D
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local notation "c" => ComplexShape.down ℕ
local notation "I" => RecursiveTotal.iter B Z
local notation "K" => barBicomplex k D
local instance : Module A N := inflatedModule D X N
local instance : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

theorem leadingTotalEmbedding_d₁ (r n i q : ℕ) (h : (i+1)+q=n+1)
    (v : (((DB).obj ((I r).X q)).X (i+1))) :
    (((K (I r)).d₁ c (i+1) q n ≫ leadingTotalEmbedding k D X N r n).hom v) =
    outerCast k D X N (show (r+q)+i=r+n by omega)
      (outerBarSuffix k D X N ((I r).X q) (r+q) i (innerTotalEmbedding k D X N r q)
        ((((DB).obj ((I r).X q)).d (i+1) i).hom v)) := by
  rw [HomologicalComplex₂.d₁_eq _ _ (by rfl : (c).Rel (i+1) i) q n (by change i+q=n; omega)]
  change (((1:ℤˣ) • ((((DB).obj ((I r).X q)).d (i+1) i) ≫
    (K (I r)).ιTotal c i q n (by change i+q=n; omega))) ≫ leadingTotalEmbedding k D X N r n).hom v = _
  erw [one_smul, Category.assoc, leadingTotalEmbedding_ι]
  rfl

theorem leadingTotalEmbedding_d₂ (r n i q : ℕ) (h : i+(q+1)=n+1)
    (v : (((DB).obj ((I r).X (q+1))).X i)) :
    (((K (I r)).d₂ c i (q+1) n ≫ leadingTotalEmbedding k D X N r n).hom v) =
    (-1:k)^i • outerCast k D X N (show (r+q)+i=r+n by omega)
      (outerBarSuffix k D X N ((I r).X (q+1)) (r+q) i
        ((innerTotalEmbedding k D X N r q).comp
          (((I r).d (q+1) q).hom.restrictScalars k)) v) := by
  rw [HomologicalComplex₂.d₂_eq _ _ i (by rfl : (c).Rel (q+1) q) n (by change i+q=n; omega)]
  change ((((-1:ℤˣ)^i) • (((DB).map ((I r).d (q+1) q)).f i ≫
    (K (I r)).ιTotal c i q n (by change i+q=n; omega))) ≫ leadingTotalEmbedding k D X N r n).hom v = _
  erw [Linear.units_smul_comp, Category.assoc, leadingTotalEmbedding_ι]
  change ((-1:ℤˣ)^i) •
    outerCast k D X N _
      (outerBarSuffix k D X N ((I r).X q) (r+q) i (innerTotalEmbedding k D X N r q)
        ((((DB).map ((I r).d (q+1) q)).f i).hom v)) = _
  rw [totalSign_smul k (D ⊗[k] term k A N (r+n)), outerBarSuffix_map]

/-- Both total faces vanish at the respective zero degree by the actual chain shape. -/
theorem leadingTotalEmbedding_d₁_zero (r n q : ℕ) :
    (K (I r)).d₁ c 0 q n ≫ leadingTotalEmbedding k D X N r n = 0 := by
  erw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by simp), zero_comp]

theorem leadingTotalEmbedding_d₂_zero (r n i : ℕ) :
    (K (I r)).d₂ c i 0 n ≫ leadingTotalEmbedding k D X N r n = 0 := by
  erw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (by simp), zero_comp]

theorem leadingTotalEmbedding_ι_d (r n i q : ℕ) (h : i+q=n+1) :
    (K (I r)).ιTotal c i q (n+1) h ≫ (barTotal k D (I r)).d (n+1) n ≫
      leadingTotalEmbedding k D X N r n =
    (K (I r)).d₁ c i q n ≫ leadingTotalEmbedding k D X N r n +
      (K (I r)).d₂ c i q n ≫ leadingTotalEmbedding k D X N r n := by
  simp only [barTotal, HomologicalComplex₂.total_d]
  erw [add_comp, comp_add, HomologicalComplex₂.ι_D₁_assoc,
    HomologicalComplex₂.ι_D₂_assoc]
end DerivedBar.ParityBridge

end

end OAI
