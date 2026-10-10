import OAI.Algebra.Finitistic.Dimension.PDBarQuotientAction
import OAI.Algebra.Finitistic.Dimension.PDBarDetection
import OAI.Algebra.Finitistic.Bar.TensorModel

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.PDBarQuotient
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The restricted scalar convention in the detector agrees with the original
compatible k action by actual tensor maps in both directions. -/
def scalarEquiv :
    (PDTensor.tensorFunctor k A (RightBase f)).obj (ModuleCat.of A V) ≃ₗ[k]
      BalancedTensor.Tensor k A (RightBase f) V :=
  LinearEquiv.ofLinearMap
    (PDTensor.mapRight (k := k) (M := PDTensor.ScalarModule k A (ModuleCat.of A V))
      (N := V) (RightBase f) LinearMap.id)
    (PDTensor.mapRight (k := k) (M := V)
      (N := PDTensor.ScalarModule k A (ModuleCat.of A V)) (RightBase f) LinearMap.id)
    (by apply BalancedTensor.ext; intros; rfl)
    (by apply BalancedTensor.ext; intros; rfl)

def nativeScalarEquiv : DerivedBar.Balanced.tensor f V ≃ₗ[k]
    (ModuleCat.restrictScalars (algebraMap k D)).obj
      (ModuleCat.of D (DerivedBar.Balanced.tensor f V)) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' c z := (IsScalarTower.algebraMap_smul D c z).symm

def objectIso :
    (PDTensor.tensorFunctor k A (RightBase f)).obj (ModuleCat.of A V) ≅
      (ModuleCat.restrictScalars (algebraMap k D)).obj
        (ModuleCat.of D (DerivedBar.Balanced.tensor f V)) :=
  (((scalarEquiv f V).trans (equiv f V)).trans (nativeScalarEquiv f V)).toModuleIso

variable {V} {W : Type u} [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
theorem objectIso_natural (h : V →ₗ[A] W) :
    (PDTensor.tensorFunctor k A (RightBase f)).map (ModuleCat.ofHom h) ≫ (objectIso f W).hom =
      (objectIso f V).hom ≫ (ModuleCat.restrictScalars (algebraMap k D)).map
        (ModuleCat.ofHom (DerivedBar.Balanced.map f V W h)) := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.ext
  intro d v
  rfl

variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- The detector's tensor of the actual bar resolution is the bar worker's
balanced complex, after restricting only its exterior scalars. -/
def barQuotientIso :
    ((PDTensor.tensorFunctor k A (RightBase f)).mapHomologicalComplex _).obj
      (DerivedBar.projectiveResolution k A N).complex ≅
    ((ModuleCat.restrictScalars (algebraMap k D)).mapHomologicalComplex _).obj
      (DerivedBar.tensorBarComplex k A D N f) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => objectIso f (DerivedBar.term k A N (n+1))) (by
      intro i j hij
      change j+1=i at hij
      subst i
      simpa only [DerivedBar.tensorBarComplex, DerivedBar.projectiveResolution, DerivedBar.complex, ChainComplex.of_d, Functor.mapHomologicalComplex_obj_d] using (objectIso_natural f (DerivedBar.differential k A N (j+1))).symm)

/-- Comparison to the literal two-sided bar complex used in the splitting. -/
def twoSidedIso :
    ((PDTensor.tensorFunctor k A (RightBase f)).mapHomologicalComplex _).obj
      (DerivedBar.projectiveResolution k A N).complex ≅
    ((ModuleCat.restrictScalars (algebraMap k D)).mapHomologicalComplex _).obj
      (DerivedBar.twoSidedComplex k A D N f) :=
  barQuotientIso f N ≪≫
    ((ModuleCat.restrictScalars (algebraMap k D)).mapHomologicalComplex _).mapIso
      (DerivedBar.tensorBarIso k A D N f)

variable [FiniteDimensional k A] [FiniteDimensional k N]
/-- Tor computed by the literal two-sided bar, with no assumed quotient comparison. -/
def torIsoTwoSided (n : ℕ) :
    PDTensor.Tor (k := k) (RightBase f) (ModuleCat.of A N) n ≅
      (((ModuleCat.restrictScalars (algebraMap k D)).mapHomologicalComplex _).obj
        (DerivedBar.twoSidedComplex k A D N f)).homology n :=
  (DerivedBar.projectiveResolution k A N).isoLeftDerivedObj
    (PDTensor.tensorFunctor k A (RightBase f)) n ≪≫
      (HomologicalComplex.homologyFunctor _ _ n).mapIso (twoSidedIso f N)
end LittleFinitistic.PDBarQuotient

end

end OAI
