import OAI.GroupTheory.PolycyclicRecognition.Algebra.BarAutomorphism
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalHomologyAction
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.QuotientCoinvariantsFiniteness

namespace OAI

/-! # Comparing subgroup conjugation with ambient bar translation

The conjugation map on the subgroup bar complex equals ambient translation
composed with the bar endomorphism already homotopic to the identity.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

theorem subgroupBarConjugation_free (g : G) (n : ℕ) :
    barAutomorphismFreeMap (MulAut.conjNormal (H := N) g) n ≫
        Rep.resMap (MulAut.conjNormal (H := N) g).toMonoidHom
          (subgroupFreeInclusion N n) =
      subgroupFreeInclusion N n ≫ Rep.resMap N.subtype (innerBarFreeMap g n) ≫
        normalHomologyCoefficient ℤ N (Rep.free ℤ G (Fin n → G)) g := by
  apply Rep.free_ext
  intro x
  change (subgroupFreeInclusion N n).hom
      ((barAutomorphismFreeMap (MulAut.conjNormal (H := N) g) n).hom
        (Finsupp.single x (MonoidAlgebra.single 1 1))) =
    (Rep.free ℤ G (Fin n → G)).ρ g
      ((innerBarFreeMap g n).hom
        ((subgroupFreeInclusion N n).hom (Finsupp.single x (MonoidAlgebra.single 1 1))))
  rw [barAutomorphismFreeMap_single, map_one, subgroupFreeInclusion_single,
    subgroupFreeInclusion_single, innerBarFreeMap_single,
    Representation.free_single_single]
  simp only [Subgroup.coe_one, one_mul, mul_inv_cancel]
  rfl

def ambientConjugationNatTrans (g : G) :
    Rep.resFunctor.{0} (k := ℤ) N.subtype ⟶
      Rep.resFunctor.{0} (k := ℤ) N.subtype ⋙
        Rep.resFunctor (k := ℤ) (MulAut.conjNormal (H := N) g).toMonoidHom where
  app A := normalHomologyCoefficient ℤ N A g
  naturality {A B} f := by
    apply Rep.hom_ext
    apply DFunLike.ext
    intro x
    exact (Rep.hom_comm_apply f g x).symm

def ambientBarTranslation (g : G) :
    ((Rep.resFunctor.{0} (k := ℤ) N.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Rep.barComplex ℤ G) ⟶
      ((Rep.resFunctor.{0} (k := ℤ) N.subtype ⋙
        Rep.resFunctor (k := ℤ) (MulAut.conjNormal (H := N) g).toMonoidHom).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (Rep.barComplex ℤ G) :=
  (NatTrans.mapHomologicalComplex (ambientConjugationNatTrans N g)
    (ComplexShape.down ℕ)).app (Rep.barComplex ℤ G)

theorem subgroupBarConjugation_chain (g : G) :
    barAutomorphismMap (MulAut.conjNormal (H := N) g) ≫
        ((Rep.resFunctor (k := ℤ) (MulAut.conjNormal (H := N) g).toMonoidHom).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (subgroupBarResolutionMap N) =
      subgroupBarResolutionMap N ≫
        ((Rep.resFunctor (k := ℤ) N.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (innerBarMap g) ≫ ambientBarTranslation N g := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact subgroupBarConjugation_free N g i

theorem quotientBar_inner_homology (g : G) (i : ℕ) :
    HomologicalComplex.homologyMap
      (((Rep.quotientToCoinvariantsFunctor.{0} ℤ N).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (innerBarMap g)) i = 𝟙 _ := by
  have h := ((Rep.quotientToCoinvariantsFunctor.{0} ℤ N).mapHomotopy
    (innerBarMapHomotopy g)).homologyMap_eq i
  let T := (Rep.quotientToCoinvariantsFunctor.{0} ℤ N).mapHomologicalComplex
    (ComplexShape.down ℕ)
  have hId : T.map (𝟙 (Rep.barComplex ℤ G)) = 𝟙 (T.obj (Rep.barComplex ℤ G)) :=
    T.map_id _
  change HomologicalComplex.homologyMap (T.map (innerBarMap g)) i =
    HomologicalComplex.homologyMap (T.map (𝟙 (Rep.barComplex ℤ G))) i at h
  rw [hId, HomologicalComplex.homologyMap_id] at h
  exact h

end PolycyclicRecognition

end

end OAI
