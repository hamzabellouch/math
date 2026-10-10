import OAI.Algebra.Finitistic.Bimodule.BimoduleComparison
import OAI.Algebra.Finitistic.Bar.BarFunctor

namespace OAI
open CategoryTheory TensorProduct
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

/-- The component comparison to the explicit two-sided bar. -/
def freeBarTensorIso (N : ModuleCat.{u} D) :
    ((barFunctor k D ⋙ (tensorFunctor k D X).mapHomologicalComplex c).obj N) ≅
      barComplex k D X N :=
  resolvedTensorIso k D X N ≪≫ tensorResolutionIso k D X N

/-- The map on the explicit field-tensor bar terms. -/
def barTermMap {V W : ModuleCat.{u} D} (f : V ⟶ W) (n : ℕ) :
    X ⊗[k] term k D V n →ₗ[D] X ⊗[k] term k D W n :=
  AlgebraTensorModule.lTensor D X ((termMap k D V W f.hom n).restrictScalars k)

theorem freeMap_termMap {V W : ModuleCat.{u} D} (f : V ⟶ W) (n : ℕ) :
    freeMap k D X _ _ (termMap k D V W f.hom (n+1)) =
      barTermMap k D X f n := by
  apply AlgebraTensorModule.ext
  intro x v
  change descend k D X _ (map k D X _ _ (termMap k D V W f.hom (n+1))
    (insert k D X _ (x ⊗ₜ[k] v))) = x ⊗ₜ[k] termMap k D V W f.hom n v
  rw [insert_tmul, map_quotient, termMap_tmul, descend_quotient,
    collapse_tmul, MulOpposite.op_one, one_smul]

theorem barDifferential_natural {V W : ModuleCat.{u} D} (f : V ⟶ W) (n : ℕ) :
    (barDifferential k D X W n).comp (barTermMap k D X f (n+1)) =
      (barTermMap k D X f n).comp (barDifferential k D X V n) := by
  rw [← freeMap_termMap, ← freeMap_termMap]
  unfold barDifferential
  rw [← freeMap_comp, ← freeMap_comp, differential_natural]

/-- The two-sided bar map is defined on literal tensor coordinates. -/
def twoSidedBarMap {V W : ModuleCat.{u} D} (f : V ⟶ W) :
    barComplex k D X V ⟶ barComplex k D X W where
  f n := ModuleCat.ofHom (barTermMap k D X f n)
  comm' i j hij := by
    change j+1=i at hij
    subst i
    apply ModuleCat.hom_ext
    simpa only [barComplex, ChainComplex.of_d, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
      using! barDifferential_natural k D X f j

/-- A functor with both maps and differential defined on the explicit bar tensors. -/
def twoSidedBarFunctor : ModuleCat.{u} D ⥤ ChainComplex (ModuleCat.{u} D) ℕ where
  obj N := barComplex k D X N
  map f := twoSidedBarMap k D X f
  map_id N := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply AlgebraTensorModule.ext
    intro x v
    change x ⊗ₜ[k] termMap k D N N LinearMap.id n v = x ⊗ₜ[k] v
    rw [termMap_id]; rfl
  map_comp {V W U} f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply AlgebraTensorModule.ext
    intro x v
    change x ⊗ₜ[k] termMap k D V U (g.hom.comp f.hom) n v =
      x ⊗ₜ[k] termMap k D W U g.hom n (termMap k D V W f.hom n v)
    rw [termMap_comp]; rfl

instance twoSidedBarFunctor_preservesZero : (twoSidedBarFunctor k D X).PreservesZeroMorphisms where
  map_zero V W := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply AlgebraTensorModule.ext
    intro x v
    change x ⊗ₜ[k] termMap k D V W 0 n v = 0
    rw [termMap_zero, LinearMap.zero_apply, TensorProduct.tmul_zero]

/-- Natural comparison, preserving the exterior D-action. -/
def freeBarTensorNatIso :
    barFunctor k D ⋙ (tensorFunctor k D X).mapHomologicalComplex c ≅
      twoSidedBarFunctor k D X :=
  NatIso.ofComponents (freeBarTensorIso k D X) (by
    intro V W f
    apply HomologicalComplex.Hom.ext
    funext n
    change (tensorFunctor k D X).map (ModuleCat.ofHom (termMap k D V W f.hom (n+1))) ≫
        (tensorFunctorObjIso k D X (term k D W (n+1))).hom ≫
        (freeEquiv k D X (term k D W n)).toModuleIso.hom =
      (tensorFunctorObjIso k D X (term k D V (n+1))).hom ≫
        (freeEquiv k D X (term k D V n)).toModuleIso.hom ≫
        ModuleCat.ofHom (barTermMap k D X f n)
    rw [← Category.assoc, tensorFunctorObjIso_natural, Category.assoc]
    congr 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (freeMap_termMap k D X f n ▸
      freeMap_descend k D X (term k D V n) (term k D W n)
        (termMap k D V W f.hom (n+1)) z).symm)

/-- The literal two-sided bar bicomplex of an arbitrary nonnegative chain input. -/
def twoSidedBarBicomplex (Z : ChainComplex (ModuleCat.{u} D) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} D) c c :=
  HomologicalComplex₂.flip (((twoSidedBarFunctor k D X).mapHomologicalComplex c).obj Z)

/-- Horizontal differential is the explicit two-sided bar, without count transport. -/
theorem twoSidedBarBicomplex_d₁ (Z : ChainComplex (ModuleCat.{u} D) ℕ) (i q : ℕ) :
    ((twoSidedBarBicomplex k D X Z).d (i+1) i).f q =
      ModuleCat.ofHom (barDifferential k D X (Z.X q) i) := by
  change (barComplex k D X (Z.X q)).d (i+1) i = _
  simp only [barComplex, ChainComplex.of_d]
end DerivedBar.BimoduleTensor

end

end OAI
