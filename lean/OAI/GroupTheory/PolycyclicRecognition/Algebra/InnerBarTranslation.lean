import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SubgroupBarResolution
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace OAI

/-! # An augmented bar-resolution lift of inner conjugation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Rep Finsupp
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem bar_d_single_single (n : ℕ) (x : Fin (n + 1) → G) (h : G) (r : ℤ) :
    (Rep.barComplex.d ℤ G n).hom (Finsupp.single x (MonoidAlgebra.single h r)) =
      Finsupp.single (fun i => x i.succ) (MonoidAlgebra.single (h * x 0) r) +
      ∑ j : Fin (n + 1), Finsupp.single (j.contractNth (· * ·) x)
        (MonoidAlgebra.single h (r * (-1 : ℤ) ^ (j.val + 1))) := by
  have he : Finsupp.single x (MonoidAlgebra.single h r) =
      r • (Rep.free ℤ G (Fin (n + 1) → G)).ρ h
        (Finsupp.single x (MonoidAlgebra.single 1 1)) := by
    rw [Representation.free_single_single, mul_one]
    simp
  rw [he, map_zsmul, Rep.hom_comm_apply, Rep.barComplex.d_single]
  simp only [map_add, map_sum, Representation.free_single_single, smul_add, Finset.smul_sum,
    Finsupp.smul_single, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]


def innerBarFreeMap (a : G) (n : ℕ) :
    Rep.free ℤ G (Fin n → G) ⟶ Rep.free ℤ G (Fin n → G) :=
  Rep.freeLift ℤ G _ (fun x =>
    Finsupp.single ((MulAut.conj a) ∘ x) (MonoidAlgebra.single a⁻¹ 1))

theorem innerBarFreeMap_single (a : G) (n : ℕ) (x : Fin n → G) (h : G) (r : ℤ) :
    (innerBarFreeMap a n).hom (Finsupp.single x (MonoidAlgebra.single h r)) =
      Finsupp.single ((MulAut.conj a) ∘ x) (MonoidAlgebra.single (h * a⁻¹) r) := by
  change Representation.freeLift (Representation.free ℤ G (Fin n → G))
    (fun x => Finsupp.single ((MulAut.conj a) ∘ x) (MonoidAlgebra.single a⁻¹ 1))
      (Finsupp.single x (MonoidAlgebra.single h r)) = _
  rw [Representation.freeLift_single_single, Representation.free_single_single]
  simp

theorem innerBarFreeMap_d (a : G) (n : ℕ) :
    innerBarFreeMap a (n + 1) ≫ Rep.barComplex.d ℤ G n =
      Rep.barComplex.d ℤ G n ≫ innerBarFreeMap a n := by
  apply Rep.free_ext
  intro x
  change (Rep.barComplex.d ℤ G n).hom
      ((innerBarFreeMap a (n + 1)).hom (Finsupp.single x (MonoidAlgebra.single 1 1))) =
    (innerBarFreeMap a n).hom
      ((Rep.barComplex.d ℤ G n).hom (Finsupp.single x (MonoidAlgebra.single 1 1)))
  rw [innerBarFreeMap_single, one_mul, bar_d_single_single, Rep.barComplex.d_single,
    map_add, map_sum, innerBarFreeMap_single]
  congr 1
  · congr 1
    simp [MulAut.conj_apply, mul_assoc]
  · apply Finset.sum_congr rfl
    intro j _
    rw [innerBarFreeMap_single, one_mul, one_mul]
    congr 1
    exact (Fin.comp_contractNth (· * ·) (· * ·)
      (f := (MulAut.conj a).toMonoidHom) (map_mul _) j x).symm

def innerBarMap (a : G) : Rep.barComplex ℤ G ⟶ Rep.barComplex ℤ G :=
  ChainComplex.ofHom (innerBarFreeMap a) (fun n => by
    simpa only [ChainComplex.of_d] using innerBarFreeMap_d a n)

theorem innerBarMap_augmentation (a : G) :
    innerBarMap a ≫ (Rep.barResolution ℤ G).π = (Rep.barResolution ℤ G).π := by
  apply HomologicalComplex.Hom.ext
  funext i
  cases i with
  | zero =>
    apply Rep.free_ext
    intro x
    change ((Rep.barResolution ℤ G).π.f 0).hom
        ((innerBarFreeMap a 0).hom (Finsupp.single x (MonoidAlgebra.single 1 1))) =
      ((Rep.barResolution ℤ G).π.f 0).hom (Finsupp.single x (MonoidAlgebra.single 1 1))
    rw [innerBarFreeMap_single, barResolution_pi_single, barResolution_pi_single]
  | succ i =>
    change (innerBarMap a).f (i + 1) ≫ (0 : (Rep.barComplex ℤ G).X (i + 1) ⟶ _) = 0
    exact CategoryTheory.Limits.comp_zero

def innerBarMapHomotopy (a : G) : Homotopy (innerBarMap a) (𝟙 (Rep.barComplex ℤ G)) := by
  have hid : (Rep.barResolution ℤ G).π ≫
      (ChainComplex.single₀ (Rep ℤ G)).map (𝟙 (Rep.trivial ℤ G ℤ)) =
      (Rep.barResolution ℤ G).π := by
    exact (congrArg (fun f => (Rep.barResolution ℤ G).π ≫ f)
      ((ChainComplex.single₀ (Rep ℤ G)).map_id (Rep.trivial ℤ G ℤ))).trans (Category.comp_id _)
  apply ProjectiveResolution.liftHomotopy (P := Rep.barResolution ℤ G)
    (Q := Rep.barResolution ℤ G) (𝟙 (Rep.trivial ℤ G ℤ))
    (innerBarMap a) (𝟙 (Rep.barComplex ℤ G))
  · exact (innerBarMap_augmentation a).trans hid.symm
  · exact (Category.id_comp (Rep.barResolution ℤ G).π).trans hid.symm

end PolycyclicRecognition

end

end OAI
