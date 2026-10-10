import OAI.GroupTheory.PolycyclicRecognition.Algebra.InnerBarTranslation

namespace OAI

/-! # The bar-resolution map induced by a group automorphism -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def barAutomorphismFreeMap (e : G ≃* G) (n : ℕ) :
    Rep.free ℤ G (Fin n → G) ⟶ Rep.res e.toMonoidHom (Rep.free ℤ G (Fin n → G)) :=
  Rep.freeLift ℤ G _ (fun x => Finsupp.single (e ∘ x) (MonoidAlgebra.single 1 1))

theorem barAutomorphismFreeMap_single (e : G ≃* G) (n : ℕ)
    (x : Fin n → G) (g : G) (r : ℤ) :
    (barAutomorphismFreeMap e n).hom (Finsupp.single x (MonoidAlgebra.single g r)) =
      Finsupp.single (e ∘ x) (MonoidAlgebra.single (e g) r) := by
  change Representation.freeLift (Rep.res e.toMonoidHom (Rep.free ℤ G (Fin n → G))).ρ
    (fun y => Finsupp.single (e ∘ y) (MonoidAlgebra.single 1 1))
      (Finsupp.single x (MonoidAlgebra.single g r)) = _
  rw [Representation.freeLift_single_single]
  change r • Representation.free ℤ G (Fin n → G) (e g)
      (Finsupp.single (e ∘ x) (MonoidAlgebra.single 1 1)) = _
  rw [Representation.free_single_single, mul_one]
  simp

theorem barAutomorphismFreeMap_d (e : G ≃* G) (n : ℕ) :
    barAutomorphismFreeMap e (n + 1) ≫ (Rep.resFunctor e.toMonoidHom).map
        (Rep.barComplex.d ℤ G n) =
      Rep.barComplex.d ℤ G n ≫ barAutomorphismFreeMap e n := by
  apply Rep.free_ext
  intro x
  change (Rep.barComplex.d ℤ G n).hom
      ((barAutomorphismFreeMap e (n + 1)).hom (Finsupp.single x (MonoidAlgebra.single 1 1))) =
    (barAutomorphismFreeMap e n).hom
      ((Rep.barComplex.d ℤ G n).hom (Finsupp.single x (MonoidAlgebra.single 1 1)))
  rw [barAutomorphismFreeMap_single, map_one, Rep.barComplex.d_single,
    Rep.barComplex.d_single, map_add, map_sum, barAutomorphismFreeMap_single]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [barAutomorphismFreeMap_single, map_one]
  congr 1
  exact (Fin.comp_contractNth (· * ·) (· * ·) (f := e.toMonoidHom)
    (map_mul _) j x).symm

def barAutomorphismMap (e : G ≃* G) : Rep.barComplex ℤ G ⟶
    ((Rep.resFunctor e.toMonoidHom).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Rep.barComplex ℤ G) :=
  ChainComplex.ofHom (barAutomorphismFreeMap e) (fun n => by
    change barAutomorphismFreeMap e (n + 1) ≫
        (Rep.resFunctor e.toMonoidHom).map ((Rep.barComplex ℤ G).d (n + 1) n) =
      (Rep.barComplex ℤ G).d (n + 1) n ≫ barAutomorphismFreeMap e n
    simpa only [ChainComplex.of_d] using barAutomorphismFreeMap_d e n)

theorem barAutomorphismFreeMap_augmentation (e : G ≃* G) :
    barAutomorphismFreeMap e 0 ≫ Rep.resMap e.toMonoidHom ((Rep.barResolution ℤ G).π.f 0) =
      (Rep.barResolution ℤ G).π.f 0 := by
  apply Rep.free_ext
  intro x
  change ((Rep.barResolution ℤ G).π.f 0).hom
      ((barAutomorphismFreeMap e 0).hom (Finsupp.single x (MonoidAlgebra.single 1 1))) =
    ((Rep.barResolution ℤ G).π.f 0).hom (Finsupp.single x (MonoidAlgebra.single 1 1))
  rw [barAutomorphismFreeMap_single, barResolution_pi_single, barResolution_pi_single]

end PolycyclicRecognition

end

end OAI
