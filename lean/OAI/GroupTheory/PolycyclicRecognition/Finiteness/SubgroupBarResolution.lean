import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ResolutionHomologyNaturality
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro

namespace OAI

/-! # Subgroup inclusions on the free bar resolution -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Rep Finsupp
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (H : Subgroup G)

def subgroupFreeInclusion (n : ℕ) :
    Rep.free ℤ H (Fin n → H) ⟶ Rep.res H.subtype (Rep.free ℤ G (Fin n → G)) :=
  Rep.freeLift ℤ H _ (fun x => Finsupp.single (H.subtype ∘ x) (MonoidAlgebra.single 1 1))

theorem subgroupFreeInclusion_single (n : ℕ) (x : Fin n → H) (h : H) (r : ℤ) :
    (subgroupFreeInclusion H n).hom (Finsupp.single x (MonoidAlgebra.single h r)) =
      Finsupp.single (H.subtype ∘ x) (MonoidAlgebra.single (h : G) r) := by
  change Representation.freeLift
    (Rep.res H.subtype (Rep.free ℤ G (Fin n → G))).ρ
    (fun y : Fin n → H => Finsupp.single (H.subtype ∘ y) (MonoidAlgebra.single 1 1))
    (Finsupp.single x (MonoidAlgebra.single h r)) = _
  rw [Representation.freeLift_single_single]
  change r • Representation.free ℤ G (Fin n → G) (h : G)
      (Finsupp.single (H.subtype ∘ x) (MonoidAlgebra.single 1 1)) = _
  rw [Representation.free_single_single, mul_one]
  simp

theorem subgroupFreeInclusion_d (n : ℕ) :
    subgroupFreeInclusion H (n + 1) ≫ (Rep.resFunctor H.subtype).map (Rep.barComplex.d ℤ G n) =
      Rep.barComplex.d ℤ H n ≫ subgroupFreeInclusion H n := by
  apply Rep.free_ext
  intro x
  change (Rep.barComplex.d ℤ G n).hom
      ((subgroupFreeInclusion H (n + 1)).hom (Finsupp.single x (MonoidAlgebra.single 1 1))) =
    (subgroupFreeInclusion H n).hom
      ((Rep.barComplex.d ℤ H n).hom (Finsupp.single x (MonoidAlgebra.single 1 1)))
  rw [subgroupFreeInclusion_single, Subgroup.coe_one, Rep.barComplex.d_single,
    Rep.barComplex.d_single, map_add, map_sum, subgroupFreeInclusion_single]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [subgroupFreeInclusion_single, Subgroup.coe_one]
  congr 1
  exact (Fin.comp_contractNth (· * ·) (· * ·) (f := H.subtype)
    (fun _ _ => rfl) j x).symm

def subgroupBarResolutionMap : Rep.barComplex ℤ H ⟶
    ((Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G)).complex :=
  ChainComplex.ofHom (subgroupFreeInclusion H) (fun n => by
    change subgroupFreeInclusion H (n + 1) ≫
        (Rep.resFunctor H.subtype).map ((Rep.barComplex ℤ G).d (n + 1) n) =
      (Rep.barComplex ℤ H).d (n + 1) n ≫ subgroupFreeInclusion H n
    simpa only [ChainComplex.of_d] using subgroupFreeInclusion_d H n)

omit H in
theorem barResolution_pi_single (x : Fin 0 → G) (g : G) (r : ℤ) :
    ((Rep.barResolution ℤ G).π.f 0).hom
      (Finsupp.single x (MonoidAlgebra.single g r)) = r := by
  change (Rep.standardComplex.ε ℤ G).hom
    ((Rep.diagonalSuccIsoFree ℤ G 0).inv.hom
      (Finsupp.single x (MonoidAlgebra.single g r))) = r
  have hx : (Rep.diagonalSuccIsoFree ℤ G 0).inv.hom
      (Finsupp.single x (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd x) r := by
    simp only [Rep.diagonalSuccIsoFree, Rep.diagonalSuccIsoTensorTrivial, Iso.trans_inv,
      Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
    have hs : (Rep.leftRegularTensorTrivialIsoFree ℤ G (Fin 0 → G)).inv.hom
        (Finsupp.single x (MonoidAlgebra.single g r)) =
        MonoidAlgebra.single g 1 ⊗ₜ[ℤ] MonoidAlgebra.single x r :=
      Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single x g r
    rw [hs]
    simp only [Action.tensorObj_V, Rep.tensor_V, Rep.tensor_ρ]
    have hμ := Representation.LinearizeMonoidal.μ_apply_single_single (k := ℤ)
      (X := Action.leftRegular G) (Y := Action.trivial G (Fin 0 → G)) g x 1 r
    have hm := Representation.linearizeMap_single (k := ℤ)
      (Action.diagonalSuccIsoTensorTrivial G 0).inv (g, x) ((1 : ℤ) * r)
    refine ((congrArg (fun z => Representation.linearizeMap
      (Action.diagonalSuccIsoTensorTrivial G 0).inv z) hμ).trans hm).trans ?_
    simp only [one_mul]
    congr 1
    exact Action.diagonalSuccIsoTensorTrivial_inv_hom_apply g x
  rw [hx]
  simp [Rep.standardComplex.ε]

theorem subgroupBarResolutionMap_π :
    subgroupBarResolutionMap H ≫
      ((Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G)).π =
        (Rep.barResolution ℤ H).π := by
  apply HomologicalComplex.Hom.ext
  funext i
  cases i with
  | zero =>
    apply Rep.free_ext
    intro x
    change ((Rep.barResolution ℤ G).π.f 0).hom
      ((subgroupFreeInclusion H 0).hom (Finsupp.single x (MonoidAlgebra.single 1 1))) =
        ((Rep.barResolution ℤ H).π.f 0).hom (Finsupp.single x (MonoidAlgebra.single 1 1))
    rw [subgroupFreeInclusion_single, barResolution_pi_single, barResolution_pi_single]
  | succ n =>
    exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
      (Rep.trivial ℤ H ℤ) (n + 1) (by omega)).eq_of_tgt _ _

def subgroupBarResolutionHomotopy : Homotopy (subgroupBarResolutionMap H)
    (ProjectiveResolution.homotopyEquiv (Rep.barResolution ℤ H)
      ((Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G))).hom := by
  have hid : (Rep.barResolution ℤ H).π ≫
      (ChainComplex.single₀ (Rep ℤ H)).map (𝟙 (Rep.trivial ℤ H ℤ)) =
      (Rep.barResolution ℤ H).π := by
    exact (congrArg (fun f => (Rep.barResolution ℤ H).π ≫ f)
      ((ChainComplex.single₀ (Rep ℤ H)).map_id (Rep.trivial ℤ H ℤ))).trans
        (Category.comp_id _)
  apply ProjectiveResolution.liftHomotopy (P := Rep.barResolution ℤ H)
    (Q := (Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G))
    (𝟙 (Rep.trivial ℤ H ℤ)) (subgroupBarResolutionMap H)
    (ProjectiveResolution.homotopyEquiv (Rep.barResolution ℤ H)
      ((Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G))).hom
  · exact (subgroupBarResolutionMap_π H).trans hid.symm
  · exact (ProjectiveResolution.homotopyEquiv_hom_π (Rep.barResolution ℤ H)
      ((Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G))).trans
        hid.symm

end PolycyclicRecognition

end

end OAI
