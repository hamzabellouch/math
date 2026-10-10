import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegralAugmentation
import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralRepresentationMap

namespace OAI

/-! # The augmentation kernel for a finitely generated group

Differences corresponding to a finite group generating set generate the
integral augmentation kernel as a left group-ring module.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra
variable {G : Type} [Group G]

def augmentationDifference (g : G) : (Representation.leftRegular ℤ G).asModule :=
  (Representation.leftRegular ℤ G).asModuleEquiv.symm
    (MonoidAlgebra.single g (1 : ℤ) - MonoidAlgebra.single 1 (1 : ℤ))

theorem augmentationDifference_mul (g h : G) :
    augmentationDifference (g * h) = MonoidAlgebra.single g (1 : ℤ) • augmentationDifference h +
      augmentationDifference g := by
  apply (Representation.leftRegular ℤ G).asModuleEquiv.injective
  simp only [map_add, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_single, one_smul, augmentationDifference,
    LinearEquiv.apply_symm_apply, map_sub, Representation.ofMulAction_single, smul_eq_mul, mul_one]
  abel

theorem augmentationDifference_inv (g : G) :
    augmentationDifference g⁻¹ = -(MonoidAlgebra.single g⁻¹ (1 : ℤ) • augmentationDifference g) := by
  apply (Representation.leftRegular ℤ G).asModuleEquiv.injective
  simp only [map_neg, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_single, one_smul, augmentationDifference,
    LinearEquiv.apply_symm_apply, map_sub, Representation.ofMulAction_single, smul_eq_mul,
    inv_mul_cancel, mul_one, neg_sub]

theorem augmentationDifference_mem_span {S : Set G} (hS : Subgroup.closure S = ⊤)
    (g : G) :
    augmentationDifference g ∈ Submodule.span ℤ[G] (augmentationDifference '' S) := by
  have hg : g ∈ Subgroup.closure S := by rw [hS]; trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact Submodule.subset_span ⟨g, hg, rfl⟩
  | one => simp [augmentationDifference]
  | mul g h _ _ hg hh =>
    rw [augmentationDifference_mul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hh) hg
  | inv g _ hg =>
    rw [augmentationDifference_inv]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hg)

theorem integralAugmentationKernel_fg [Group.FG G] :
    (LinearMap.ker (integralRepresentationMap
      (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1))).FG := by
  obtain ⟨S, hS, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let N := Submodule.span ℤ[G] (augmentationDifference '' S)
  have hsub (x : ℤ[G]) : (Representation.leftRegular ℤ G).asModuleEquiv.symm
      (x - MonoidAlgebra.single 1 (integralAugmentation G x)) ∈ N := by
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      simpa only [map_add, MonoidAlgebra.single_add, add_sub_add_comm] using N.add_mem hx hy
    | single g r =>
      have hg := N.smul_mem (MonoidAlgebra.single 1 r) (augmentationDifference_mem_span hS g)
      convert hg using 1
      apply (Representation.leftRegular ℤ G).asModuleEquiv.injective
      simp [augmentationDifference,
        integralAugmentation_single, smul_sub]
      rfl
  have hNK : N ≤ LinearMap.ker (integralRepresentationMap
      (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, rfl⟩
    change integralAugmentation G (MonoidAlgebra.single g (1 : ℤ) - MonoidAlgebra.single 1 (1 : ℤ)) = 0
    simp
  have hKN : LinearMap.ker (integralRepresentationMap
      (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1)) ≤ N := by
    intro x hx
    have hx' : integralAugmentation G ((Representation.leftRegular ℤ G).asModuleEquiv x) = 0 := hx
    simpa only [hx', MonoidAlgebra.single_zero, sub_zero,
      LinearEquiv.symm_apply_apply] using hsub ((Representation.leftRegular ℤ G).asModuleEquiv x)
  rw [le_antisymm hKN hNK]
  exact Submodule.fg_span (hfin.image _)

end PolycyclicRecognition

end

end OAI
