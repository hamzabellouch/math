import OAI.Algebra.Finitistic.Bar.RecursiveSuffixCoefficient
import OAI.Algebra.Finitistic.Bar.LeadingBarSuffix

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
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local notation "c" => ComplexShape.down ℕ
local notation "I" => RecursiveTotal.iter B Z
local instance : Module A N := inflatedModule D X N
local instance : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

/-- The exterior D bar is assembled on its actual finite totalization diagonal. -/
def leadingTotalEmbedding (r n : ℕ) :
    (barTotal k D (I r)).X n ⟶ ModuleCat.of D (D ⊗[k] term k A N (r+n)) :=
  totalMapDesc (𝟭 _) (barBicomplex k D (I r)) (fun i q h =>
    ModuleCat.ofHom ((outerCast k D X N (show (r+q)+i=r+n by omega)).comp
      (outerBarSuffix k D X N ((I r).X q) (r+q) i (innerTotalEmbedding k D X N r q))))

@[reassoc (attr := simp)] theorem leadingTotalEmbedding_ι (r n i q : ℕ) (h : i+q=n) :
    (barBicomplex k D (I r)).ιTotal c i q n h ≫ leadingTotalEmbedding k D X N r n =
      ModuleCat.ofHom ((outerCast k D X N (show (r+q)+i=r+n by omega)).comp
        (outerBarSuffix k D X N ((I r).X q) (r+q) i (innerTotalEmbedding k D X N r q))) := by
  exact ι_totalMapDesc (𝟭 _) (barBicomplex k D (I r)) _ i q h

/-- The independently recursive inner total is the previously constructed explicit multibar. -/
theorem innerIter_eq_explicit (r : ℕ) : I r = explicitMultibar k D X r Z := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [RecursiveTotal.iter, RecursiveTotal.bicomplex, ih, explicitMultibar,
      BimoduleTensor.explicitBarTotal, BimoduleTensor.twoSidedBarBicomplex]
end DerivedBar.ParityBridge

end

end OAI
