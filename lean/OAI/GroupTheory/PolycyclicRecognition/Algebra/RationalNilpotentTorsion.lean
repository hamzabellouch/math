import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalAbelianTorsion
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentFiniteRankRootCore

namespace OAI

/-! # A nilpotent group with zero rational abelianization is torsion

The last lower-central layer is a quotient of a tensor product whose first
factor is the abelianization. The proof works for every nilpotency class and
does not require finite generation.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct IsMulCommutative commutatorElement
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

theorem rational_abelianization_isZero_of_surjective {Q : Type} [Group Q]
    (f : G →* Q) (hf : Function.Surjective f)
    (hG : IsZero (ModuleCat.of ℚ (RationalAbelianSpace (Abelianization G)))) :
    IsZero (ModuleCat.of ℚ (RationalAbelianSpace (Abelianization Q))) :=
  rational_module_isZero_of_surjective (Abelianization.map f).toAdditive.toIntLinearMap
    (abelianization_map_surjective f hf) hG

theorem lowerCentral_torsion_of_rational_abelianization_isZero (n : ℕ)
    (hbound : (⊤ : Subgroup G).lowerCentralSeries n = ⊥)
    (hG : IsZero (ModuleCat.of ℚ (RationalAbelianSpace (Abelianization G)))) :
    ∀ g : G, IsOfFinOrder g := by
  induction n generalizing G with
  | zero =>
    intro g
    have hg : g = 1 := by
      have hm : g ∈ (⊤ : Subgroup G) := Subgroup.mem_top g
      rw [show (⊤ : Subgroup G) = ⊥ from hbound] at hm
      exact hm
    rw [hg]
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨1, Nat.zero_lt_one, one_pow 1⟩
  | succ n ih =>
    cases n with
    | zero =>
      let : IsMulCommutative G := (commutator_eq_bot_iff G).mp hbound
      let e : Additive (Abelianization G) ≃ₗ[ℤ] Additive G :=
        (Abelianization.equivOfComm (H := G)).symm.toAdditive.toIntLinearEquiv
      have hz := rational_module_isZero_of_surjective e.toLinearMap e.surjective hG
      exact rationalAbelianSpace_isZero_iff_torsion.mp hz
    | succ n =>
      let J := (⊤ : Subgroup G).lowerCentralSeries (n + 1)
      let N := (⊤ : Subgroup G).lowerCentralSeries n
      have hJcenter : J ≤ Subgroup.center G :=
        Subgroup.commutator_top_right_eq_bot_iff_le_center.mp hbound
      have hC : ⁅(⊤ : Subgroup G), N⁆ = J := Subgroup.commutator_comm _ _
      let q := QuotientGroup.mk' J
      have hq : Function.Surjective q := QuotientGroup.mk'_surjective J
      have hQbound : (⊤ : Subgroup (G ⧸ J)).lowerCentralSeries (n + 1) = ⊥ := by
        have hJmap : J.map q = ⊥ := by
          rw [Subgroup.map_eq_bot_iff]
          exact le_of_eq (QuotientGroup.ker_mk' J).symm
        have he := Subgroup.map_lowerCentralSeries (⊤ : Subgroup G) q (n + 1)
        rw [Subgroup.map_top, q.range_eq_top_of_surjective hq] at he
        exact he.symm.trans hJmap
      have hQt := ih hQbound (rational_abelianization_isZero_of_surjective q hq hG)
      let f := q.comp N.subtype
      have hAc : f.range ≤ Subgroup.center (G ⧸ J) := by
        rintro _ ⟨b, rfl⟩
        rw [Subgroup.mem_center_iff]
        intro a
        obtain ⟨g, rfl⟩ := hq a
        apply commutatorElement_eq_one_iff_mul_comm.mp
        change ⁅q g, q (b : G)⁆ = 1
        rw [← map_commutatorElement]
        apply (QuotientGroup.eq_one_iff _).mpr
        rw [← hC]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) b.property
      let : IsMulCommutative f.range := ⟨⟨fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.mp (hAc a.property) b).symm⟩⟩
      let K := f.ker
      let e := QuotientGroup.quotientKerEquivRange f
      let : IsMulCommutative (N ⧸ K) := ⟨⟨fun a b => e.injective (by
        rw [map_mul, map_mul, mul_comm])⟩⟩
      have hKc : K.map N.subtype ≤ Subgroup.center G := by
        rintro _ ⟨b, hb, rfl⟩
        apply hJcenter
        exact (QuotientGroup.eq_one_iff _).mp hb
      have hCc : ⁅(⊤ : Subgroup G), N⁆ ≤ Subgroup.center G := hC ▸ hJcenter
      let : IsMulCommutative J := ⟨⟨fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.mp (hJcenter a.property) b).symm⟩⟩
      let : IsMulCommutative (⁅(⊤ : Subgroup G), N⁆ : Subgroup G) := hC.symm ▸ inferInstance
      have hT := rational_tensor_isZero (Additive (Abelianization G)) (Additive (N ⧸ K)) hG
      have hL := rational_module_isZero_of_surjective
        (centralLayerTensorSurjection N hCc K hKc)
        (centralLayerTensor_surjective N hCc K hKc) hT
      let e₁ : centralLayerSubmodule N ≃ₗ[ℤ] Additive (⁅(⊤ : Subgroup G), N⁆ : Subgroup G) :=
        (centralLayerAddEquiv N hCc).toIntLinearEquiv
      let e₂ : Additive (⁅(⊤ : Subgroup G), N⁆ : Subgroup G) ≃ₗ[ℤ] Additive J :=
        (MulEquiv.subgroupCongr hC).toAdditive.toIntLinearEquiv
      let eL := e₁.trans e₂
      have hJ := rational_module_isZero_of_surjective eL.toLinearMap eL.surjective hL
      have hJt : ∀ z : J, IsOfFinOrder z := rationalAbelianSpace_isZero_iff_torsion.mp hJ
      intro g
      obtain ⟨k, hk, hg⟩ := (hQt (q g)).exists_pow_eq_one
      have hgJ : g ^ k ∈ J := (QuotientGroup.eq_one_iff _).mp (by
        change q (g ^ k) = 1
        rw [map_pow]
        exact hg)
      obtain ⟨m, hm, hgm⟩ := (hJt ⟨g ^ k, hgJ⟩).exists_pow_eq_one
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨k * m, Nat.mul_pos hk hm, ?_⟩
      rw [pow_mul]
      exact congrArg Subtype.val hgm

theorem nilpotent_torsion_of_rational_abelianization_isZero [Group.IsNilpotent G]
    (hG : IsZero (ModuleCat.of ℚ (RationalAbelianSpace (Abelianization G)))) :
    ∀ g : G, IsOfFinOrder g :=
  lowerCentral_torsion_of_rational_abelianization_isZero (Group.nilpotencyClass G)
    (Subgroup.lowerCentralSeries_nilpotencyClass (G := G)) hG

end PolycyclicRecognition

end

end OAI
