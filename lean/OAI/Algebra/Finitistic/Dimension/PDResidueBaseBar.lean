import OAI.Algebra.Finitistic.Dimension.PDResidueAssociativity
import OAI.Algebra.Finitistic.Dimension.PDBaseBarConsumer
import OAI.Algebra.Finitistic.Bar.SplitProjectiveTail

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped TensorProduct
namespace LittleFinitistic.PDResidueAssociativity
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]

/-- Scalar restriction coherence for an arbitrary right tensor factor. -/
def scalarTensorEquiv {R : Type u} [Ring R] [Algebra k R]
    (U V : Type u) [AddCommGroup U] [Module k U] [Module Rᵐᵒᵖ U]
    [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V] :
    (PDTensor.tensorFunctor k R U).obj (ModuleCat.of R V) ≃ₗ[k] BalancedTensor.Tensor k R U V :=
  LinearEquiv.ofLinearMap
    (PDTensor.mapRight (k := k) (M := PDTensor.ScalarModule k R (ModuleCat.of R V)) (N := V) U LinearMap.id)
    (PDTensor.mapRight (k := k) (M := V) (N := PDTensor.ScalarModule k R (ModuleCat.of R V)) U LinearMap.id)
    (by apply BalancedTensor.ext; intros; rfl) (by apply BalancedTensor.ext; intros; rfl)

variable (f : A →ₐ[k] D)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
local notation "S" => PDTensor.Residue (A := D)
local notation "SA" => PDResidueProjection.InflatedResidue f

def objectIso : (PDTensor.tensorFunctor k A SA).obj (ModuleCat.of A V) ≅
    (PDTensor.tensorFunctor k D S).obj (ModuleCat.of D (DerivedBar.Balanced.tensor f V)) :=
  (((scalarTensorEquiv SA V).trans (equiv f V).symm).trans
    (scalarTensorEquiv S (DerivedBar.Balanced.tensor f V)).symm).toModuleIso

variable {V} {W : Type u} [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
theorem objectIso_natural (h : V →ₗ[A] W) :
    (PDTensor.tensorFunctor k A SA).map (ModuleCat.ofHom h) ≫ (objectIso f W).hom =
      (objectIso f V).hom ≫ (PDTensor.tensorFunctor k D S).map
        (ModuleCat.ofHom (DerivedBar.Balanced.map f V W h)) := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.ext
  intro s v
  rfl

variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

def barIso :
    ((PDTensor.tensorFunctor k A SA).mapHomologicalComplex _).obj (DerivedBar.projectiveResolution k A N).complex ≅
      ((PDTensor.tensorFunctor k D S).mapHomologicalComplex _).obj (DerivedBar.tensorBarComplex k A D N f) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => objectIso f (DerivedBar.term k A N (n+1))) (by
    intro i j hij
    change j+1=i at hij
    subst i
    simpa only [DerivedBar.tensorBarComplex, DerivedBar.projectiveResolution, DerivedBar.complex,
      ChainComplex.of_d, Functor.mapHomologicalComplex_obj_d] using
      (objectIso_natural f (DerivedBar.differential k A N (j+1))).symm)

def twoSidedIso :
    ((PDTensor.tensorFunctor k A SA).mapHomologicalComplex _).obj (DerivedBar.projectiveResolution k A N).complex ≅
      ((PDTensor.tensorFunctor k D S).mapHomologicalComplex _).obj (DerivedBar.twoSidedComplex k A D N f) :=
  barIso f N ≪≫ ((PDTensor.tensorFunctor k D S).mapHomologicalComplex _).mapIso
    (DerivedBar.tensorBarIso k A D N f)

variable (hf : Function.Surjective f)
variable (hsq : ∀ a ∈ RingHom.ker f.toRingHom, ∀ b ∈ RingHom.ker f.toRingHom, a*b=0)

/-- Actual residue Tor is computed by tensoring the free D-bar with D/rad D.
This proves the needed change-of-rings comparison on the actual models. -/
def residueTorIso (n : ℕ) : PDTensor.Tor (k := k) (PDTensor.Residue (A := A)) (ModuleCat.of A N) n ≅
    (((PDTensor.tensorFunctor k D S).mapHomologicalComplex _).obj
      (DerivedBar.twoSidedComplex k A D N f)).homology n :=
  PDResidueProjection.torIso f hf hsq (ModuleCat.of A N) (DerivedBar.projectiveResolution k A N) n ≪≫
    (DerivedBar.projectiveResolution k A N).isoLeftDerivedObj (PDTensor.tensorFunctor k A SA) n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (twoSidedIso f N)

/-- The actual D-bar has projective terms, even when its length is infinite. -/
theorem twoSided_projective (n : ℕ) : Projective ((DerivedBar.twoSidedComplex k A D N f).X n) := by
  have : Module.Free D (D ⊗[k] DerivedBar.term k A N n) :=
    Module.Free.of_basis (Algebra.TensorProduct.basis D (Module.Free.chooseBasis k (DerivedBar.term k A N n)))
  change Projective (ModuleCat.of D (D ⊗[k] DerivedBar.term k A N n))
  infer_instance

include hf hsq

variable [FiniteDimensional k A] [FiniteDimensional k N]

/-- Bounded D-derived bar homology suffices for finite pd over A. The
exact-tail theorem supplies the amplitude after residue tensor. -/
theorem finite_pd_of_bounded_base_bar (g : ℕ) (hg : ∀ M : ModuleCat.{u} D, HasProjectiveDimensionLE M g)
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero ((DerivedBar.twoSidedComplex k A D N f).homology n)) :
    projectiveDimension (ModuleCat.of A N) < ⊤ := by
  apply PDTensor.projectiveDimension_lt_top_of_bounded_residueTor (PDMinimal.FiniteModule.of (k := k) (A := A) N)
  obtain ⟨b,hb⟩ := h
  refine ⟨b+g+3, fun n hn => ?_⟩
  have he : ∀ i, b+1 ≤ i → (DerivedBar.twoSidedComplex k A D N f).ExactAt i := by
    intro i hi
    exact ((DerivedBar.twoSidedComplex k A D N f).exactAt_iff_isZero_homology i).mpr (hb i (by omega))
  have ht := DerivedBar.ProjectiveTail.map_exact_tail (DerivedBar.twoSidedComplex k A D N f)
    (PDTensor.tensorFunctor k D S) (b+1) g he (twoSided_projective f N) hg n (by omega)
  exact ht.isZero_homology.of_iso (residueTorIso f N hf hsq n)

local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} D) := HasDerivedCategory.standard (ModuleCat.{u} D)

theorem finite_pd_of_base_derived_iso (g : ℕ) (hg : ∀ M : ModuleCat.{u} D, HasProjectiveDimensionLE M g)
    (Z : DerivedCategory (ModuleCat.{u} D)) (e : PDBarQuotient.baseDerived f N ≅ Z)
    (h : ∃ b : ℕ, ∀ n, b < n → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).obj Z)) :
    projectiveDimension (ModuleCat.of A N) < ⊤ := by
  apply finite_pd_of_bounded_base_bar f N hf hsq g hg
  obtain ⟨b,hb⟩ := h
  refine ⟨b,fun n hn => ?_⟩
  exact (hb n hn).of_iso
    (((DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).mapIso e.symm) ≪≫
      PDBarQuotient.baseDerivedHomologyIso f N n).symm
end LittleFinitistic.PDResidueAssociativity

end

end OAI
