import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteAugmentationFromFP
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteAugmentationKernel
import Mathlib.GroupTheory.GroupAction.Quotient

namespace OAI

/-! # FP one implies finite generation

The finite supports of augmentation-kernel generators generate the group.
Projection to the permutation module on their left cosets proves this directly.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G]

def integralCosetProjection (K : Subgroup G) :
    Rep.leftRegular ℤ G ⟶ Rep.ofMulAction ℤ G (G ⧸ K) :=
  Rep.leftRegularHom _ (MonoidAlgebra.single (QuotientGroup.mk 1) 1)

@[simp] theorem integralCosetProjection_single (K : Subgroup G) (g : G) (r : ℤ) :
    (integralCosetProjection K).hom (MonoidAlgebra.single g r) =
      MonoidAlgebra.single (QuotientGroup.mk g) r := by
  simp [integralCosetProjection,
    Representation.ofMulAction_single, smul_eq_mul]

theorem integralCosetProjection_support (K : Subgroup G) (c : ℤ[G])
    (hc : ∀ g ∈ c.coeff.support, g ∈ K) :
    (integralCosetProjection K).hom c =
      MonoidAlgebra.single (QuotientGroup.mk 1) (integralAugmentation G c) := by
  classical
  let L := (integralCosetProjection K).hom.toLinearMap -
    (MonoidAlgebra.lsingle (QuotientGroup.mk (1 : G) : G ⧸ K)).comp (integralAugmentation G)
  have hL : L c = 0 := by
    conv_lhs => rw [← MonoidAlgebra.sum_coeff_single c, map_finsuppSum]
    apply Finset.sum_eq_zero
    intro g hg
    have hcoset : (QuotientGroup.mk g : G ⧸ K) = QuotientGroup.mk 1 :=
      QuotientGroup.eq.mpr (by simpa using K.inv_mem (hc g hg))
    change (integralCosetProjection K).hom (MonoidAlgebra.single g (c.coeff g)) -
      MonoidAlgebra.single (QuotientGroup.mk 1)
        (integralAugmentation G (MonoidAlgebra.single g (c.coeff g))) = 0
    rw [integralCosetProjection_single, integralAugmentation_single, hcoset, sub_self]
  exact sub_eq_zero.mp hL

theorem mem_subgroup_of_coset_difference_zero (K : Subgroup G) (g : G)
    (hp : (integralCosetProjection K).hom
      (MonoidAlgebra.single g (1 : ℤ) - MonoidAlgebra.single 1 (1 : ℤ)) = 0) : g ∈ K := by
  classical
  have hsub : MonoidAlgebra.single (QuotientGroup.mk g : G ⧸ K) (1 : ℤ) -
      MonoidAlgebra.single (QuotientGroup.mk 1 : G ⧸ K) (1 : ℤ) = 0 := by
    calc
      _ = (integralCosetProjection K).hom
          (MonoidAlgebra.single g (1 : ℤ) - MonoidAlgebra.single 1 (1 : ℤ)) := by
        rw [map_sub, integralCosetProjection_single, integralCosetProjection_single]
      _ = 0 := hp
  have heq : (QuotientGroup.mk g : G ⧸ K) = QuotientGroup.mk 1 := by
    by_contra hne
    have he := congrArg (fun c : ℤ[G ⧸ K] => c.coeff (QuotientGroup.mk g))
      (sub_eq_zero.mp hsub)
    simp [hne] at he
  have hmem := QuotientGroup.eq.mp heq
  simpa using K.inv_mem hmem

theorem mem_subgroup_of_module_difference_zero (K : Subgroup G) (g : G)
    (hp : augmentationDifference g ∈
      LinearMap.ker (integralRepresentationMap (integralCosetProjection K))) : g ∈ K := by
  apply mem_subgroup_of_coset_difference_zero K g
  exact hp

theorem augmentationDifference_mem_kernel (g : G) :
    augmentationDifference g ∈ LinearMap.ker (integralRepresentationMap
      (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1)) := by
  change integralAugmentation G
    (MonoidAlgebra.single g (1 : ℤ) - MonoidAlgebra.single 1 (1 : ℤ)) = 0
  simp

theorem group_fg_of_augmentationKernel_fg
    (hfg : (LinearMap.ker (integralRepresentationMap
      (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1))).FG) : Group.FG G := by
  classical
  let A := Rep.leftRegular ℤ G
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp hfg
  let S : Set G := ⋃ a ∈ s, ((A.ρ.asModuleEquiv a).coeff.support : Set G)
  have hS : S.Finite := hs.biUnion fun a _ => (A.ρ.asModuleEquiv a).coeff.support.finite_toSet
  let K := Subgroup.closure S
  have hgen (a) (ha : a ∈ s) :
      integralRepresentationMap (integralCosetProjection K) a = 0 := by
    have haker : a ∈ LinearMap.ker (integralRepresentationMap
        (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1)) := by
      rw [← hspan]
      exact Submodule.subset_span ha
    have hau : integralAugmentation G (A.ρ.asModuleEquiv a) = 0 := haker
    change (integralCosetProjection K).hom (A.ρ.asModuleEquiv a) = 0
    rw [integralCosetProjection_support K _ (fun g hg =>
      Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, hg⟩⟩)),
      hau, MonoidAlgebra.single_zero]
  have hker : LinearMap.ker (integralRepresentationMap
      (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1)) ≤
      LinearMap.ker (integralRepresentationMap (integralCosetProjection K)) := by
    rw [← hspan]
    exact Submodule.span_le.mpr hgen
  have hK : K = ⊤ := by
    apply top_unique
    intro g _
    exact mem_subgroup_of_module_difference_zero K g
      (hker (augmentationDifference_mem_kernel g))
  exact (Group.fg_iff).mpr ⟨S, hK, hS⟩

theorem TypeFP.fg (hG : TypeFP G 1) : Group.FG G :=
  group_fg_of_augmentationKernel_fg hG.augmentationKernel_fg

theorem TypeFPInfinity.fg (hG : TypeFPInfinity G) : Group.FG G := (hG 1).fg

theorem HasFiniteProjectiveResolution.fg (hG : HasFiniteProjectiveResolution G) :
    Group.FG G := (hG.typeFPInfinity G).fg

end PolycyclicRecognition

end

end OAI
