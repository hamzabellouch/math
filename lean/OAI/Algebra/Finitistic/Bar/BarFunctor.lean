import OAI.Algebra.Finitistic.Bar.Bar
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Category.ModuleCat.Colimits

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory
noncomputable section

namespace DerivedBar
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (V W U : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
  [AddCommGroup U] [Module k U] [Module A U] [IsScalarTower k A U]

/-- Functorial map on every augmented bar term. -/
def termMap (h : V →ₗ[A] W) : (n : ℕ) → term k A V n →ₗ[A] term k A W n
  | 0 => h
  | n+1 => AlgebraTensorModule.lTensor A A ((termMap h n).restrictScalars k)

@[simp] theorem termMap_tmul (h : V →ₗ[A] W) (n : ℕ) (a : A) (v : term k A V n) :
    termMap k A V W h (n+1) (a ⊗ₜ[k] v) = a ⊗ₜ[k] termMap k A V W h n v := rfl

theorem termMap_comp (h : V →ₗ[A] W) (g : W →ₗ[A] U) (n : ℕ) :
    termMap k A V U (g.comp h) n = (termMap k A W U g n).comp (termMap k A V W h n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply AlgebraTensorModule.ext
    intro a v
    change a ⊗ₜ[k] termMap k A V U (g.comp h) n v =
      a ⊗ₜ[k] termMap k A W U g n (termMap k A V W h n v)
    rw [ih]
    rfl

theorem termMap_id (n : ℕ) : termMap k A V V LinearMap.id n = LinearMap.id := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply AlgebraTensorModule.ext
    intro a v
    change a ⊗ₜ[k] termMap k A V V LinearMap.id n v = a ⊗ₜ[k] v
    rw [ih]
    rfl

theorem termMap_zero (n : ℕ) : termMap k A V W 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply AlgebraTensorModule.ext
    intro a v
    change a ⊗ₜ[k] termMap k A V W 0 n v = 0
    rw [ih, LinearMap.zero_apply, TensorProduct.tmul_zero]

/-- The bar differential is natural for all module maps. -/
theorem differential_natural (h : V →ₗ[A] W) (n : ℕ) :
    (differential k A W n).comp (termMap k A V W h (n+1)) =
      (termMap k A V W h n).comp (differential k A V n) := by
  induction n with
  | zero =>
    apply AlgebraTensorModule.ext
    intro a v
    exact (h.map_smul a v).symm
  | succ n ih =>
    apply AlgebraTensorModule.ext
    intro a v
    have hn : differential k A W n (termMap k A V W h (n+1) v) =
        termMap k A V W h n (differential k A V n v) := LinearMap.congr_fun ih v
    change a • termMap k A V W h (n+1) v -
        a ⊗ₜ[k] differential k A W n (termMap k A V W h (n+1) v) =
      termMap k A V W h (n+1) (a • v - a ⊗ₜ[k] differential k A V n v)
    rw [map_sub, map_smul]
    change a • termMap k A V W h (n+1) v -
        a ⊗ₜ[k] differential k A W n (termMap k A V W h (n+1) v) =
      a • termMap k A V W h (n+1) v -
        a ⊗ₜ[k] termMap k A V W h n (differential k A V n v)
    rw [hn]

/-- Unit insertion is natural over k, the key homotopy for the total bar augmentation. -/
theorem contraction_natural (h : V →ₗ[A] W) (n : ℕ) (v : term k A V n) :
    termMap k A V W h (n+1) (contraction k A V n v) =
      contraction k A W n (termMap k A V W h n v) := rfl

/-- An actual chain map between unaugmented free bar resolutions. -/
def complexMap (h : V →ₗ[A] W) : complex k A V ⟶ complex k A W where
  f n := ModuleCat.ofHom (termMap k A V W h (n+1))
  comm' i j hij := by
    change j+1 = i at hij
    subst i
    apply ModuleCat.hom_ext
    simpa only [complex, ChainComplex.of_d, ModuleCat.hom_comp, ModuleCat.hom_ofHom] using!
      differential_natural k A V W h (j+1)

local instance (N : ModuleCat.{u} A) : Module k N := Module.compHom N (algebraMap k A)
local instance (N : ModuleCat.{u} A) : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- The explicit free bar resolution is functorial, not just an objectwise choice. -/
def barFunctor : ModuleCat.{u} A ⥤ ChainComplex (ModuleCat.{u} A) ℕ where
  obj N := complex k A N
  map h := complexMap k A _ _ h.hom
  map_id N := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    exact termMap_id k A N (n+1)
  map_comp h g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    exact termMap_comp k A _ _ _ h.hom g.hom (n+1)

instance barFunctor_preservesZero : (barFunctor k A).PreservesZeroMorphisms where
  map_zero V W := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    exact termMap_zero k A V W (n+1)

/-- The bicomplex for the left-module bar resolution of a nonnegative chain complex.
Outer degree is the bar length; inner degree is the input complex degree.
The two differentials commute by the proved naturality of the absolute bar differential. -/
def barBicomplex (Z : ChainComplex (ModuleCat.{u} A) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  HomologicalComplex₂.flip (((barFunctor k A).mapHomologicalComplex (ComplexShape.down ℕ)).obj Z)

/-- Each entry in the bar bicomplex is genuinely projective over A. -/
instance barBicomplex_projective (Z : ChainComplex (ModuleCat.{u} A) ℕ) (i q : ℕ) :
    Projective (((barBicomplex k A Z).X i).X q) := by
  change Projective ((complex k A (Z.X q)).X i)
  exact complex_projective k A (Z.X q) i

/-- The ordinary direct-sum total bar complex, with standard totalization signs.
The total augmentation quasi-isomorphism must still be proved. -/
def barTotal (Z : ChainComplex (ModuleCat.{u} A) ℕ) :
    ChainComplex (ModuleCat.{u} A) ℕ :=
  (barBicomplex k A Z).total (ComplexShape.down ℕ)

end DerivedBar

end

end OAI
