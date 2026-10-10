import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.NoetherianTor

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section RingGroupHomology

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
attribute [local instance 1200] Rep.hV2
namespace RingCoinvariants
variable {G : Type} [CommGroup G]
local notation "R" => MonoidAlgebra ℤ G

noncomputable def augmentation : R →+* ℤ :=
  (MonoidAlgebra.lift ℤ ℤ G (1 : G →* ℤ)).toRingHom

@[simp] theorem augmentation_of (g : G) :
    augmentation (MonoidAlgebra.of ℤ G g) = 1 :=
  MonoidAlgebra.lift_of _ _

noncomputable def augmentationTrivialIso :
    Rep.ofModuleMonoidAlgebra.obj (NoetherianResolution.augmentationModule
      (augmentation (G := G))) ≅ Rep.trivial ℤ G ℤ := by
  refine (moduleRepIso _).symm ≪≫ Rep.mkIso ?_
  refine { (LinearEquiv.refl ℤ ℤ) with isIntertwining' := ?_ }
  intro g
  apply LinearMap.ext
  intro x
  change augmentation (MonoidAlgebra.of ℤ G g) • x = x
  rw [augmentation_of, one_smul]

instance : (Rep.ofModuleMonoidAlgebra (k := ℤ) (G := G)).Additive where
  map_add := by intros; rfl

variable [IsNoetherianRing (MonoidAlgebra ℤ G)]

noncomputable def groupResolution : ProjectiveResolution (Rep.trivial ℤ G ℤ) := by
  let Q := Rep.ofModuleMonoidAlgebra.mapProjectiveResolution
    (NoetherianResolution.augmentationResolution (augmentation (G := G)))
  exact {
    complex := Q.complex
    projective := Q.projective
    π := Q.π ≫ (ChainComplex.single₀ (Rep ℤ G)).map augmentationTrivialIso.hom }

noncomputable def complexIso (L : FGModuleCat R) :
    (groupResolution (G := G)).complex.coinvariantsTensorObj (inverseRep L.obj) ≅
      ((ModuleCat.restrictScalars (Int.castRingHom R)).mapHomologicalComplex _).obj
        (NoetherianResolution.augmentationComplex augmentation L) :=
  (CategoryTheory.Functor.mapHomologicalComplexCompIso (functorIso L.obj)
    (ComplexShape.down ℕ)).app
      (NoetherianResolution.augmentationResolution (augmentation (G := G))).complex

theorem finite_groupHomology_inverse (L : FGModuleCat R) (n : ℕ) :
    Module.Finite ℤ (groupHomology (inverseRep L.obj) n) := by
  classical
  let C := NoetherianResolution.augmentationComplex (augmentation (G := G)) L
  let F := ModuleCat.restrictScalars (Int.castRingHom R)
  let := NoetherianResolution.finite_int_augmentation_homology augmentation L n
  let e0 : ModuleCat.of ℤ (C.homology n) ≅ F.obj (C.homology n) := intRestrictionIso _
  have : Module.Finite ℤ (F.obj (C.homology n)) :=
    Module.Finite.of_surjective e0.hom.hom e0.toLinearEquiv.surjective
  let e1 : ((F.mapHomologicalComplex _).obj C).homology n ≅
      F.obj (C.homology n) := (C.sc n).mapHomologyIso F
  have : Module.Finite ℤ (((F.mapHomologicalComplex _).obj C).homology n) :=
    Module.Finite.of_surjective e1.inv.hom e1.toLinearEquiv.symm.surjective
  let e2 := HomologicalComplex.homologyMapIso (complexIso L) n
  have : Module.Finite ℤ (((groupResolution (G := G)).complex.coinvariantsTensorObj
      (inverseRep L.obj)).homology n) :=
    Module.Finite.of_surjective e2.inv.hom e2.toLinearEquiv.symm.surjective
  let e3 := groupHomologyIso (inverseRep L.obj) n (groupResolution (G := G))
  exact Module.Finite.of_surjective e3.inv.hom e3.toLinearEquiv.symm.surjective

end RingCoinvariants
end RingGroupHomology

section FiniteAbelianHomology

open CategoryTheory
attribute [local instance 1200] Rep.hV2
namespace RingCoinvariants
variable {G : Type} [CommGroup G] [IsNoetherianRing (MonoidAlgebra ℤ G)]

noncomputable def inverseHomologyIso (A : Rep ℤ G) (n : ℕ) :
    groupHomology (inverseRep (ModuleCat.of (MonoidAlgebra ℤ G) A.ρ.asModule)) n ≅
      groupHomology A n := by
  let e : (inverseRep (ModuleCat.of (MonoidAlgebra ℤ G) A.ρ.asModule)) ≃+ A := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl }
  refine groupHomology.mapIso
    (A := inverseRep (ModuleCat.of (MonoidAlgebra ℤ G) A.ρ.asModule)) (B := A)
    (MulEquiv.inv G) (e.toIntLinearEquiv) ?_ n
  intro g
  apply DFunLike.ext
  intro x
  change A.ρ.asAlgebraHom (MonoidAlgebra.single g⁻¹ 1) x = A.ρ g⁻¹ x
  rw [Representation.asAlgebraHom_single_one]

theorem finite_groupHomology (A : Rep ℤ G)
    [Module.Finite (MonoidAlgebra ℤ G) A.ρ.asModule] (n : ℕ) :
    Module.Finite ℤ (groupHomology A n) := by
  let L := FGModuleCat.of (MonoidAlgebra ℤ G) A.ρ.asModule
  have := finite_groupHomology_inverse L n
  let e := inverseHomologyIso A n
  exact Module.Finite.of_surjective e.hom.hom e.toLinearEquiv.surjective

end RingCoinvariants
end FiniteAbelianHomology

end SimpleAmenable
end
end

end OAI
