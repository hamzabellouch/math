import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ProjectiveCoefficientHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.QuotientResolutionHomology

namespace OAI

/-! # Homology in the ambient-resolution direction

Fixing a free right tensor factor gives the actual finite-support functor.
The comparison computes the columns of the normal-extension bicomplex, with
the normal subgroup's ordinary integral homology as coefficients.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2200] TensorProduct.instModule
attribute [local instance 2300] Representation.Coinvariants.instModule Finsupp.module
variable {G : Type} [Group G]

def rightCoinvariantsFunctor (B : Rep.{0} ℤ G) : Rep.{0} ℤ G ⥤ ModuleCat ℤ where
  obj A := ((Rep.coinvariantsTensor ℤ G).obj A).obj B
  map f := ((Rep.coinvariantsTensor ℤ G).map f).app B
  map_id A := by
    change ((Rep.coinvariantsTensor ℤ G).map (𝟙 A)).app B = _
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    change ((Rep.coinvariantsTensor ℤ G).map (f ≫ g)).app B = _
    rw [CategoryTheory.Functor.map_comp]
    rfl

instance (B : Rep.{0} ℤ G) : (rightCoinvariantsFunctor B).PreservesZeroMorphisms where
  map_zero A C := by
    change ((Rep.coinvariantsTensor ℤ G).map (0 : A ⟶ C)).app B = 0
    rw [Functor.map_zero]
    rfl

def rightFreeCoinvariantsIso (ι : Type) :
    rightCoinvariantsFunctor (Rep.free ℤ G ι) ≅
      forget₂ (Rep.{0} ℤ G) (ModuleCat ℤ) ⋙ moduleFinsuppFunctor ℤ ι := by
  classical
  refine NatIso.ofComponents (fun A => (Rep.coinvariantsTensorFreeLEquiv A ι).toModuleIso) ?_
  intro A B f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let L : ((Rep.coinvariantsTensor ℤ G).obj A).obj (Rep.free ℤ G ι) →ₗ[ℤ] (ι →₀ B) :=
    ((rightCoinvariantsFunctor (Rep.free ℤ G ι)).map f ≫
      (Rep.coinvariantsTensorFreeLEquiv B ι).toModuleIso.hom).hom
  let R : ((Rep.coinvariantsTensor ℤ G).obj A).obj (Rep.free ℤ G ι) →ₗ[ℤ] (ι →₀ B) :=
    ((Rep.coinvariantsTensorFreeLEquiv A ι).toModuleIso.hom ≫
      (forget₂ (Rep.{0} ℤ G) (ModuleCat ℤ) ⋙ moduleFinsuppFunctor ℤ ι).map f).hom
  change L x = R x
  induction x using Representation.Coinvariants.induction_on with
  | h x =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a u => exact tensorFreeToFinsupp_natural ι A B f a u

instance rightFreeCoinvariants_preservesHomology (ι : Type) :
    (rightCoinvariantsFunctor (Rep.free ℤ G ι)).PreservesHomology := by
  classical
  let F := forget₂ (Rep.{0} ℤ G) (ModuleCat ℤ) ⋙ moduleFinsuppFunctor ℤ ι
  let : PreservesFiniteLimits (moduleFinsuppFunctor ℤ ι) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  let : PreservesFiniteColimits (moduleFinsuppFunctor ℤ ι) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  let : PreservesFiniteLimits F := by dsimp [F]; infer_instance
  let : PreservesFiniteColimits F := by dsimp [F]; infer_instance
  let : PreservesFiniteLimits (rightCoinvariantsFunctor (Rep.free ℤ G ι)) :=
    preservesFiniteLimits_of_natIso (rightFreeCoinvariantsIso (G := G) ι).symm
  let : PreservesFiniteColimits (rightCoinvariantsFunctor (Rep.free ℤ G ι)) :=
    preservesFiniteColimits_of_natIso (rightFreeCoinvariantsIso (G := G) ι).symm
  infer_instance

variable (N : Subgroup G) [N.Normal]

def normalExtensionColumnHomologyIso
    (P : ProjectiveResolution (trivialIntegral G)) (i j : ℕ) :
    ((normalExtensionBicomplex N P).flip.X j).homology i ≅
      ModuleCat.of ℤ ((Fin j → G ⧸ N) →₀ groupHomology (Rep.trivial ℤ N ℤ) i) := by
  classical
  let C := normalQuotientResolutionComplex N P
  let F := rightCoinvariantsFunctor (Rep.free ℤ (G ⧸ N) (Fin j → G ⧸ N))
  change (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C).homology i) ≅ _
  exact (C.sc i).mapHomologyIso F ≪≫
    (rightFreeCoinvariantsIso (G := G ⧸ N) (Fin j → G ⧸ N)).app (C.homology i) ≪≫
      (moduleFinsuppFunctor ℤ (Fin j → G ⧸ N)).mapIso (quotientResolutionHomologyIso N P i)

end PolycyclicRecognition

end

end OAI
