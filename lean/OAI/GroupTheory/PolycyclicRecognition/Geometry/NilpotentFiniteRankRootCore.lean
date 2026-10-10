import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralLayerTensor
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootCoreAbelianRank
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CentralExtensionRootCore

namespace OAI

/-! # Finite root cores from the rational abelianization of a nilpotent group

Induction uses the last lower-central layer. Its commutator tensor
presentation is finite because the preceding layer is an abelian subgroup
of the quotient, where a finite root core has already been constructed.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct IsMulCommutative commutatorElement
variable {G Q : Type} [Group G] [Group Q]

theorem abelianization_map_surjective (f : G →* Q) (hf : Function.Surjective f) :
    Function.Surjective (Abelianization.map f) := by
  intro a
  induction a using QuotientGroup.induction_on with | H a =>
    obtain ⟨g, rfl⟩ := hf a
    exact ⟨Abelianization.of g, rfl⟩

theorem rational_abelianization_finite_of_surjective (f : G →* Q)
    (hf : Function.Surjective f)
    [Module.Finite ℚ (RationalAbelianSpace (Abelianization G))] :
    Module.Finite ℚ (RationalAbelianSpace (Abelianization Q)) :=
  Module.Finite.of_surjective ((Abelianization.map f).toAdditive.toIntLinearMap.baseChange ℚ)
    ((Abelianization.map f).toAdditive.toIntLinearMap.baseChange_surjective ℚ
      (abelianization_map_surjective f hf))

theorem lowerCentral_rootCore_of_finite_abelianization (n : ℕ)
    (hbound : (⊤ : Subgroup G).lowerCentralSeries n = ⊥)
    [Module.Finite ℚ (RationalAbelianSpace (Abelianization G))] :
    ∃ H : Subgroup G, H.FG ∧ ∀ g, ∃ m : ℕ, 0 < m ∧ g ^ m ∈ H := by
  induction n generalizing G with
  | zero =>
    have hg (g : G) : g = 1 := by
      have hm : g ∈ (⊤ : Subgroup G) := Subgroup.mem_top g
      rw [show (⊤ : Subgroup G) = ⊥ from hbound] at hm
      exact hm
    exact ⟨⊥, Subgroup.FG.bot, fun g => ⟨1, by omega, by simp [hg g]⟩⟩
  | succ n ih =>
    cases n with
    | zero =>
      let : IsMulCommutative G := (commutator_eq_bot_iff G).mp hbound
      let e : Additive (Abelianization G) ≃ₗ[ℤ] Additive G :=
        (Abelianization.equivOfComm (H := G)).symm.toAdditive.toIntLinearEquiv
      let : Module.Finite ℚ (RationalAbelianSpace G) :=
        Module.Finite.of_surjective (e.baseChange ℤ ℚ _ _).toLinearMap
          (e.baseChange ℤ ℚ _ _).surjective
      exact abelian_finiteRank_rootCore
    | succ n =>
      let J := (⊤ : Subgroup G).lowerCentralSeries (n + 1)
      let N := (⊤ : Subgroup G).lowerCentralSeries n
      have hJcenter : J ≤ Subgroup.center G :=
        Subgroup.commutator_top_right_eq_bot_iff_le_center.mp hbound
      have hC : ⁅(⊤ : Subgroup G), N⁆ = J :=
        Subgroup.commutator_comm _ _
      let q := QuotientGroup.mk' J
      have hq : Function.Surjective q := QuotientGroup.mk'_surjective J
      have hJmap : J.map q = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        exact le_of_eq (QuotientGroup.ker_mk' J).symm
      have hQbound : (⊤ : Subgroup (G ⧸ J)).lowerCentralSeries (n + 1) = ⊥ := by
        have he := Subgroup.map_lowerCentralSeries (⊤ : Subgroup G) q (n + 1)
        rw [Subgroup.map_top, q.range_eq_top_of_surjective hq] at he
        exact he.symm.trans hJmap
      let : Module.Finite ℚ (RationalAbelianSpace (Abelianization (G ⧸ J))) :=
        rational_abelianization_finite_of_surjective q hq
      obtain ⟨H, hH, hroot⟩ := ih hQbound
      let : Group.IsNilpotent (G ⧸ J) :=
        Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨n + 1, hQbound⟩
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
      let : Module.Finite ℚ (RationalAbelianSpace f.range) :=
        nilpotent_rootCore_abelian_subgroup_finite H hH hroot f.range
      let K := f.ker
      let e := QuotientGroup.quotientKerEquivRange f
      let : IsMulCommutative (N ⧸ K) := ⟨⟨fun a b => e.injective (by
        rw [map_mul, map_mul, mul_comm])⟩⟩
      let : Module.Finite ℚ (RationalAbelianSpace (N ⧸ K)) :=
        Module.Finite.of_surjective (e.symm.toAdditive.toIntLinearEquiv.baseChange ℤ ℚ _ _).toLinearMap
          (e.symm.toAdditive.toIntLinearEquiv.baseChange ℤ ℚ _ _).surjective
      have hKc : K.map N.subtype ≤ Subgroup.center G := by
        rintro _ ⟨b, hb, rfl⟩
        apply hJcenter
        exact (QuotientGroup.eq_one_iff _).mp hb
      have hCc : ⁅(⊤ : Subgroup G), N⁆ ≤ Subgroup.center G := hC ▸ hJcenter
      let : IsMulCommutative J := ⟨⟨fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.mp (hJcenter a.property) b).symm⟩⟩
      let : IsMulCommutative (⁅(⊤ : Subgroup G), N⁆ : Subgroup G) := hC.symm ▸ inferInstance
      have hfin := central_commutator_scalar_finite N hCc K hKc ℚ
      let : Module.Finite ℚ (RationalAbelianSpace J) := by
        let := hfin
        let eJ : Additive (⁅(⊤ : Subgroup G), N⁆ : Subgroup G) ≃ₗ[ℤ] Additive J :=
          (MulEquiv.subgroupCongr hC).toAdditive.toIntLinearEquiv
        exact Module.Finite.of_surjective (eJ.baseChange ℤ ℚ _ _).toLinearMap
          (eJ.baseChange ℤ ℚ _ _).surjective
      exact central_extension_rootCore J hJcenter abelian_finiteRank_rootCore ⟨H, hH, hroot⟩

theorem nilpotent_rootCore_of_finite_abelianization [Group.IsNilpotent G]
    [Module.Finite ℚ (RationalAbelianSpace (Abelianization G))] :
    ∃ H : Subgroup G, H.FG ∧ ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H :=
  lowerCentral_rootCore_of_finite_abelianization (Group.nilpotencyClass G)
    (Subgroup.lowerCentralSeries_nilpotencyClass (G := G))

end PolycyclicRecognition

end

end OAI
