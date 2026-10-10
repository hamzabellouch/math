import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

namespace OAI

/-! # A coefficient-natural comparison with a projective resolution

The comparison uses the bar resolution and a fixed homotopy equivalence of
projective resolutions, so changing coefficients commutes with it.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex Rep
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] {A B : Rep ℤ G}

def coefficientTensorChainMap (P : ChainComplex (Rep ℤ G) ℕ) (f : A ⟶ B) :
    P.coinvariantsTensorObj A ⟶ P.coinvariantsTensorObj B :=
  (NatTrans.mapHomologicalComplex ((Rep.coinvariantsTensor ℤ G).map f)
    (ComplexShape.down ℕ)).app P

theorem inhomogeneousChainsIso_coefficient [DecidableEq G] (f : A ⟶ B) :
    groupHomology.chainsMap (MonoidHom.id G) f ≫ (groupHomology.inhomogeneousChainsIso B).hom =
      (groupHomology.inhomogeneousChainsIso A).hom ≫
        coefficientTensorChainMap (barComplex ℤ G) f := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro a
  change (groupHomology.inhomogeneousChainsIso B).hom.f i
      ((groupHomology.chainsMap (MonoidHom.id G) f).f i (Finsupp.single x a)) =
    (coefficientTensorChainMap (barComplex ℤ G) f).f i
      ((groupHomology.inhomogeneousChainsIso A).hom.f i (Finsupp.single x a))
  rw [groupHomology.chainsMap_f_single]
  change Rep.finsuppToCoinvariantsTensorFree B (Fin i → G) (Finsupp.single x (f.hom a)) =
    (coefficientTensorChainMap (barComplex ℤ G) f).f i
      (Rep.finsuppToCoinvariantsTensorFree A (Fin i → G) (Finsupp.single x a))
  rw [Rep.finsuppToCoinvariantsTensorFree_single, Rep.finsuppToCoinvariantsTensorFree_single]
  rfl

def coefficientNaturalHomologyIso [DecidableEq G]
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ)) (A : Rep ℤ G) (n : ℕ) :
    groupHomology A n ≅ (P.complex.coinvariantsTensorObj A).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
      (groupHomology.inhomogeneousChainsIso A) ≪≫
    isoOfQuasiIsoAt
      (((Rep.coinvariantsTensor ℤ G).obj A).mapHomotopyEquiv
        (ProjectiveResolution.homotopyEquiv (barResolution ℤ G) P)).hom n

theorem coefficientNaturalHomologyIso_naturality [DecidableEq G]
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ)) (f : A ⟶ B) (n : ℕ) :
    groupHomology.map (MonoidHom.id G) f n ≫ (coefficientNaturalHomologyIso P B n).hom =
      (coefficientNaturalHomologyIso P A n).hom ≫
        HomologicalComplex.homologyMap (coefficientTensorChainMap P.complex f) n := by
  let u : barComplex ℤ G ⟶ P.complex :=
    (ProjectiveResolution.homotopyEquiv (barResolution ℤ G) P).hom
  have hn := (NatTrans.mapHomologicalComplex ((Rep.coinvariantsTensor ℤ G).map f)
    (ComplexShape.down ℕ)).naturality u
  change (((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex _).map u ≫
      coefficientTensorChainMap P.complex f =
    coefficientTensorChainMap (barComplex ℤ G) f ≫
      (((Rep.coinvariantsTensor ℤ G).obj B).mapHomologicalComplex _).map u at hn
  have hc : groupHomology.chainsMap (MonoidHom.id G) f ≫
      ((groupHomology.inhomogeneousChainsIso B).hom ≫
        (((Rep.coinvariantsTensor ℤ G).obj B).mapHomologicalComplex _).map u) =
      ((groupHomology.inhomogeneousChainsIso A).hom ≫
        (((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex _).map u) ≫
          coefficientTensorChainMap P.complex f := by
    rw [← Category.assoc, inhomogeneousChainsIso_coefficient, Category.assoc]
    rw [← hn, ← Category.assoc]
  change HomologicalComplex.homologyMap (groupHomology.chainsMap (MonoidHom.id G) f) n ≫
      (HomologicalComplex.homologyMap (groupHomology.inhomogeneousChainsIso B).hom n ≫
        HomologicalComplex.homologyMap
          ((((Rep.coinvariantsTensor ℤ G).obj B).mapHomologicalComplex _).map u) n) =
    (HomologicalComplex.homologyMap (groupHomology.inhomogeneousChainsIso A).hom n ≫
      HomologicalComplex.homologyMap
        ((((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex _).map u) n) ≫
      HomologicalComplex.homologyMap (coefficientTensorChainMap P.complex f) n
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun v => HomologicalComplex.homologyMap v n) hc

end PolycyclicRecognition

end

end OAI
