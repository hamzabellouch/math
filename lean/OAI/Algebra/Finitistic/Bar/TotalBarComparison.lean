import OAI.Algebra.Finitistic.Bar.TotalMap
import OAI.Algebra.Finitistic.Bar.TwoSidedBarFunctor
import OAI.Algebra.Finitistic.Bar.TotalBarTensor

namespace OAI
open CategoryTheory CategoryTheory.Preadditive
open scoped TensorProduct
noncomputable section
namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance (N : ModuleCat.{u} D) : Module k N := scalarModule k D N
local instance (N : ModuleCat.{u} D) : IsScalarTower k D N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local notation "c" => ComplexShape.down ℕ

/-- The termwise balanced/free comparison is an isomorphism of bicomplexes. -/
def tensorBarBicomplexIso (Z : ChainComplex (ModuleCat.{u} D) ℕ) :
    mapBicomplex (tensorFunctor k D X) (barBicomplex k D Z) ≅
      twoSidedBarBicomplex k D X Z :=
  (HomologicalComplex₂.flipFunctor _ c c).mapIso
    ((NatIso.mapHomologicalComplex (freeBarTensorNatIso k D X) c).app Z)

/-- The explicit two-sided total bar on a nonnegative chain complex. -/
def explicitBarTotal (Z : ChainComplex (ModuleCat.{u} D) ℕ) :
    ChainComplex (ModuleCat.{u} D) ℕ :=
  (twoSidedBarBicomplex k D X Z).total c

/-- Resolving the whole input and applying balanced tensor gives precisely the
explicit two-sided bar total. Finite diagonal sums suffice; X need not be flat. -/
def tensorTotalExplicitIso (Z : ChainComplex (ModuleCat.{u} D) ℕ) :
    (tensorTotalFunctor k D X).obj Z ≅ explicitBarTotal k D X Z :=
  totalMapIso (tensorFunctor k D X) (barBicomplex k D Z) ≪≫
    HomologicalComplex₂.total.mapIso (tensorBarBicomplexIso k D X Z) c

/-- Actual horizontal endpoint-minus-tail face in the explicit bicomplex. -/
theorem explicitBar_horizontal (Z : ChainComplex (ModuleCat.{u} D) ℕ)
    (i q : ℕ) (x : X) (z : term k D (Z.X q) (i+1)) :
    (((twoSidedBarBicomplex k D X Z).d (i+1) i).f q).hom (x ⊗ₜ[k] z) =
      collapse k D X (term k D (Z.X q) i) (x ⊗ₜ[k] z) -
        x ⊗ₜ[k] differential k D (Z.X q) i z := by
  rw [twoSidedBarBicomplex_d₁]
  exact barDifferential_tmul k D X (Z.X q) i x z

/-- Actual vertical differential applies the input differential to the last factor. -/
theorem explicitBar_vertical (Z : ChainComplex (ModuleCat.{u} D) ℕ)
    (i q q' : ℕ) :
    ((twoSidedBarBicomplex k D X Z).X i).d q q' =
      ModuleCat.ofHom (barTermMap k D X (Z.d q q') i) := rfl

/-- Horizontal differential in the explicit total. -/
theorem explicitBarTotal_d₁_succ (Z : ChainComplex (ModuleCat.{u} D) ℕ)
    (i q n : ℕ) (h : i+q=n) :
    (twoSidedBarBicomplex k D X Z).d₁ c (i+1) q n =
      ModuleCat.ofHom (barDifferential k D X (Z.X q) i) ≫
        (twoSidedBarBicomplex k D X Z).ιTotal c i q n h := by
  rw [HomologicalComplex₂.d₁_eq _ _ (by rfl : (c).Rel (i+1) i) q n h]
  change (1 : ℤˣ) • (_ ≫ _) = _
  rw [one_smul, twoSidedBarBicomplex_d₁]
  rfl

/-- Standard vertical totalization sign, independent of the count differential. -/
theorem explicitBarTotal_d₂_succ (Z : ChainComplex (ModuleCat.{u} D) ℕ)
    (i q n : ℕ) (h : i+q=n) :
    (twoSidedBarBicomplex k D X Z).d₂ c i (q+1) n =
      ((-1 : ℤˣ)^i) • (ModuleCat.ofHom (barTermMap k D X (Z.d (q+1) q) i) ≫
        (twoSidedBarBicomplex k D X Z).ιTotal c i q n h) := by
  rw [HomologicalComplex₂.d₂_eq _ _ i (by rfl : (c).Rel (q+1) q) n h]
  rfl

@[simp] theorem explicitBarTotal_d₁_zero (Z : ChainComplex (ModuleCat.{u} D) ℕ)
    (q n : ℕ) : (twoSidedBarBicomplex k D X Z).d₁ c 0 q n = 0 := by
  apply HomologicalComplex₂.d₁_eq_zero
  simp

@[simp] theorem explicitBarTotal_d₂_zero (Z : ChainComplex (ModuleCat.{u} D) ℕ)
    (i n : ℕ) : (twoSidedBarBicomplex k D X Z).d₂ c i 0 n = 0 := by
  apply HomologicalComplex₂.d₂_eq_zero
  simp
end DerivedBar.BimoduleTensor

end

end OAI
