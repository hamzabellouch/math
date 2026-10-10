import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RepCochainMaps
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

namespace OAI

/-! # Coefficient naturality for cohomology from a chosen resolution

The comparison uses one fixed homotopy equivalence with the bar resolution.
Consequently it commutes with every coefficient morphism.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] {A B : Rep.{0} ℤ G}

theorem repCochainPrecomp_postcomp {P Q : ChainComplex (Rep.{0} ℤ G) ℕ}
    (u : P ⟶ Q) (f : A ⟶ B) :
    repCochainPrecomp ℤ u A ≫ repCochainPostcomp ℤ P f =
      repCochainPostcomp ℤ Q f ≫ repCochainPrecomp ℤ u B := by
  ext i v
  change (u.f i ≫ v) ≫ f = u.f i ≫ (v ≫ f)
  exact Category.assoc _ _ _

theorem inhomogeneousCochainsIso_coefficient (f : A ⟶ B) :
    groupCohomology.cochainsMap (MonoidHom.id G) f ≫
        (groupCohomology.inhomogeneousCochainsIso B).hom =
      (groupCohomology.inhomogeneousCochainsIso A).hom ≫
        repCochainPostcomp ℤ (Rep.barComplex ℤ G) f := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply DFunLike.ext
  intro v
  change (Fin i → G) → A at v
  apply Rep.free_ext
  intro t
  change B.ρ.freeLift (fun x => f.hom (v x))
      (Finsupp.single t (MonoidAlgebra.single 1 1)) =
    f.hom (A.ρ.freeLift v (Finsupp.single t (MonoidAlgebra.single 1 1)))
  simp only [Representation.freeLift_single_single, map_one, Module.End.one_apply]
  exact (f.hom.map_smul (1 : ℤ) (v t)).symm

def coefficientNaturalCohomologyIso
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ)) (A : Rep.{0} ℤ G) (n : ℕ) :
    groupCohomology A n ≅ (P.complex.linearYonedaObj ℤ A).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n).mapIso
      (groupCohomology.inhomogeneousCochainsIso A) ≪≫
    isoOfQuasiIsoAt
      (repCochainHomotopyEquiv ℤ
        (ProjectiveResolution.homotopyEquiv P (Rep.barResolution ℤ G)) A).hom n

theorem coefficientNaturalCohomologyIso_naturality
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ)) (f : A ⟶ B) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) f n ≫
        (coefficientNaturalCohomologyIso P B n).hom =
      (coefficientNaturalCohomologyIso P A n).hom ≫
        homologyMap (repCochainPostcomp ℤ P.complex f) n := by
  let u : P.complex ⟶ Rep.barComplex ℤ G :=
    (ProjectiveResolution.homotopyEquiv P (Rep.barResolution ℤ G)).hom
  have hc : groupCohomology.cochainsMap (MonoidHom.id G) f ≫
      ((groupCohomology.inhomogeneousCochainsIso B).hom ≫ repCochainPrecomp ℤ u B) =
    ((groupCohomology.inhomogeneousCochainsIso A).hom ≫ repCochainPrecomp ℤ u A) ≫
      repCochainPostcomp ℤ P.complex f := by
    rw [← Category.assoc, inhomogeneousCochainsIso_coefficient,
      Category.assoc, ← repCochainPrecomp_postcomp, ← Category.assoc]
  change homologyMap (groupCohomology.cochainsMap (MonoidHom.id G) f) n ≫
      (homologyMap (groupCohomology.inhomogeneousCochainsIso B).hom n ≫
        homologyMap (repCochainPrecomp ℤ u B) n) =
    (homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n ≫
      homologyMap (repCochainPrecomp ℤ u A) n) ≫
        homologyMap (repCochainPostcomp ℤ P.complex f) n
  simpa only [homologyMap_comp] using congrArg (fun c => homologyMap c n) hc

end PolycyclicRecognition

end

end OAI
