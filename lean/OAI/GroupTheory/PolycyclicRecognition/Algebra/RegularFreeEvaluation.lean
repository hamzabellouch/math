import OAI.GroupTheory.PolycyclicRecognition.Algebra.RegularDualPairing
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RegularDualFree

namespace OAI

/-! # Evaluation for finite free group-ring modules -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2200] TensorProduct.instModule
attribute [local instance 2300] Representation.Coinvariants.instModule Pi.Function.module
variable {G : Type} [Group G]

private def regularFreeEvaluationAddEquiv (ι : Type) [Finite ι] [DecidableEq ι] (A : Rep ℤ G) :
    ((Rep.coinvariantsTensor ℤ G).obj A).obj (Rep.free ℤ G ι) ≃+
      (regularDual (Rep.free ℤ G ι) ⟶ A) := by
  classical
  let : Module ℤ (ι →₀ A) := Finsupp.module _ _
  exact (Rep.coinvariantsTensorFreeLEquiv A ι).toAddEquiv.trans
    ((Finsupp.linearEquivFunOnFinite ℤ A ι).toAddEquiv.trans
      ((Rep.freeLiftLEquiv ℤ G ι A).symm.toAddEquiv.trans
        (Linear.homCongr ℤ (regularDualFreeIso ι).symm (Iso.refl A)).toAddEquiv))

def regularFreeEvaluationEquiv (ι : Type) [Finite ι] [DecidableEq ι] (A : Rep ℤ G) :
    ((Rep.coinvariantsTensor ℤ G).obj A).obj (Rep.free ℤ G ι) ≃ₗ[ℤ]
      (regularDual (Rep.free ℤ G ι) ⟶ A) where
  __ := regularFreeEvaluationAddEquiv ι A
  map_smul' r x := map_intCast_smul (regularFreeEvaluationAddEquiv ι A) ℤ ℤ r x

private theorem freeLiftLEquiv_symm_apply (ι : Type) (A : Rep ℤ G) (f : ι → A) :
    (Rep.freeLiftLEquiv ℤ G ι A).symm f = Rep.freeLift ℤ G A f := by
  with_unfolding_all rfl

theorem regularFreeEvaluationEquiv_precompose (ι : Type) [Finite ι] [DecidableEq ι]
    (A : Rep ℤ G)
    (x : ((Rep.coinvariantsTensor ℤ G).obj A).obj (Rep.free ℤ G ι)) :
    (regularDualFreeIso ι).inv ≫ regularFreeEvaluationEquiv ι A x =
      Rep.freeLift ℤ G A (fun j => (Rep.coinvariantsTensorFreeLEquiv A ι x) j) := by
  change (regularDualFreeIso ι).inv ≫
    Linear.homCongr ℤ (regularDualFreeIso ι).symm (Iso.refl A)
      ((Rep.freeLiftLEquiv ℤ G ι A).symm
        ((Finsupp.linearEquivFunOnFinite ℤ A ι)
          (Rep.coinvariantsTensorFreeLEquiv A ι x))) = _
  simp only [Linear.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id,
    Iso.inv_hom_id_assoc, freeLiftLEquiv_symm_apply]
  congr 1

theorem regularFreeEvaluationEquiv_eq (ι : Type) [Finite ι] [DecidableEq ι] (A : Rep ℤ G) :
    (regularFreeEvaluationEquiv ι A).toLinearMap =
      regularCoinvariantEvaluation (Rep.free ℤ G ι) A := by
  classical
  apply Representation.Coinvariants.hom_ext
  apply TensorProduct.ext
  apply DFunLike.ext
  intro a
  apply Finsupp.lhom_ext'
  intro i
  apply MonoidAlgebra.lhom_ext'
  intro g
  apply DFunLike.ext
  intro r
  apply (cancel_epi (regularDualFreeIso ι).inv).mp
  change (regularDualFreeIso ι).inv ≫ regularFreeEvaluationEquiv ι A
      (Rep.coinvariantsTensorMk A (Rep.free ℤ G ι) a
        (Finsupp.single i (MonoidAlgebra.single g r))) =
    (regularDualFreeIso ι).inv ≫ regularCoinvariantEvaluation (Rep.free ℤ G ι) A
      (Rep.coinvariantsTensorMk A (Rep.free ℤ G ι) a
        (Finsupp.single i (MonoidAlgebra.single g r)))
  rw [regularFreeEvaluationEquiv_precompose]
  apply Rep.free_ext
  intro j
  change Representation.freeLift A.ρ
      (fun k => (Rep.coinvariantsTensorFreeLEquiv A ι
        (Rep.coinvariantsTensorMk A (Rep.free ℤ G ι) a
          (Finsupp.single i (MonoidAlgebra.single g r)))) k)
        (Finsupp.single j (MonoidAlgebra.single 1 1)) = _
  rw [Representation.freeLift_single_single]
  simp only [map_one, Module.End.one_apply]
  rw [@one_smul ℤ A _ A.hV2.toMulAction]
  change (Rep.coinvariantsTensorFreeLEquiv A ι
        (Rep.coinvariantsTensorMk A (Rep.free ℤ G ι) a
          (Finsupp.single i (MonoidAlgebra.single g r)))) j =
    regularCoefficientAction A
      (((regularDualFreeIso ι).inv.hom
        (Finsupp.single j (MonoidAlgebra.single 1 1))).hom
          (Finsupp.single i (MonoidAlgebra.single g r))) a
  rw [regularDualFreeIso_inv_single]
  change (Rep.coinvariantsTensorFreeToFinsupp A ι
      (Representation.Coinvariants.mk _
        (a ⊗ₜ[ℤ] Finsupp.single i (MonoidAlgebra.single g r)))) j = _
  have ht := congrArg (fun z : ι →₀ A => z j)
    (Rep.coinvariantsTensorFreeToFinsupp_mk_tmul_single A a i g r)
  calc
    _ = (Finsupp.single i (A.hV2.smul r (A.ρ g⁻¹ a))) j := ht
    _ = _ := by
      by_cases h : i = j
      · subst j
        simp only [Finsupp.single_eq_same, regularInversion_single, inv_one,
          Representation.ofMulAction_single, smul_eq_mul, mul_one, map_smul,
          regularCoefficientAction_single, int_smul_eq_zsmul, one_smul]
        exact (map_zsmul (LinearMap.applyₗ (R := ℤ) (M := A) a) r (A.ρ g⁻¹)).symm
      · simp only [Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne (Ne.symm h),
          map_zero, smul_zero, LinearMap.zero_apply]

end PolycyclicRecognition

end

end OAI
