import OAI.GroupTheory.PolycyclicRecognition.Algebra.LocallyNilpotentTorsion
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace OAI

/-! # A finite normal kernel has finitely many conjugation actions -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem finite_normal_conjugation_cover (N : Subgroup G) [N.Normal] [Finite N] :
    ∃ H : Subgroup G, H.FG ∧ N ≤ H ∧
      ∀ g : G, ∃ h : H, ∀ x : N, g * x * g⁻¹ = (h : G) * x * (h : G)⁻¹ := by
  let ρ : G →* MulAut N := MulAut.conjNormal
  let : Finite (MulAut N) := Finite.of_injective
    (fun a : MulAut N => (a : N → N)) DFunLike.coe_injective
  let : Group.FG ρ.range := inferInstance
  obtain ⟨K, hK, hs⟩ := exists_fg_subgroup_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hN : N.FG := (Group.fg_iff_subgroup_fg N).mp inferInstance
  let H := K ⊔ N
  refine ⟨H, hK.sup hN, le_sup_right, ?_⟩
  intro g
  obtain ⟨h, hh⟩ := hs ⟨ρ g, ⟨g, rfl⟩⟩
  refine ⟨⟨h, (show K ≤ H from le_sup_left) h.property⟩, ?_⟩
  intro x
  have he : ρ (h : G) = ρ g := congrArg Subtype.val hh
  exact (congrArg (fun a : MulAut N => (a x : G)) he).symm


open scoped commutatorElement

theorem nilpotent_of_locallyNilpotent_finite_kernel
    (N : Subgroup G) [N.Normal] [Finite N] [Group.IsNilpotent (G ⧸ N)]
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H) :
    Group.IsNilpotent G := by
  obtain ⟨H, hH, hNH, hcover⟩ := finite_normal_conjugation_cover N
  let := hlocal H hH
  let n := Group.nilpotencyClass (G ⧸ N)
  let c := Group.nilpotencyClass H
  have hn : (⊤ : Subgroup G).lowerCentralSeries n ≤ N := by
    have hmap : ((⊤ : Subgroup G).lowerCentralSeries n).map (QuotientGroup.mk' N) = ⊥ := by
      rw [Subgroup.map_lowerCentralSeries, Subgroup.map_top,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)]
      exact Subgroup.lowerCentralSeries_nilpotencyClass
    simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hmap
  have hs : ∀ k : ℕ, (⊤ : Subgroup G).lowerCentralSeries (n + k) ≤ N ∧
      (⊤ : Subgroup G).lowerCentralSeries (n + k) ≤ H.lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact ⟨by simpa using hn, by simpa using hn.trans hNH⟩
    | succ k ih =>
      constructor
      · rw [Nat.add_succ, Subgroup.lowerCentralSeries_succ]
        exact (Subgroup.commutator_mono ih.1 le_rfl).trans (Subgroup.commutator_le_left N ⊤)
      · rw [Nat.add_succ, Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ]
        apply Subgroup.commutator_le.mpr
        intro x hx g _
        obtain ⟨h, hh⟩ := hcover g
        have he := hh ⟨x⁻¹, N.inv_mem (ih.1 hx)⟩
        have hcomm : ⁅x, g⁆ = ⁅x, (h : G)⁆ := by
          simpa only [commutatorElement_def, mul_assoc] using congrArg (fun y => x * y) he
        rw [hcomm]
        exact Subgroup.commutator_mem_commutator (ih.2 hx) h.property
  apply Subgroup.nilpotent_iff_lowerCentralSeries.mpr
  refine ⟨n + c, eq_bot_iff.mpr ?_⟩
  exact (hs c).2.trans (le_of_eq (Subgroup.lowerCentralSeries_eq_bot_of_nilpotencyClass_le (S := H) le_rfl))

end PolycyclicRecognition

end

end OAI
