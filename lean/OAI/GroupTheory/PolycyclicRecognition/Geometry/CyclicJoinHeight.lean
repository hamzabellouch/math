import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntegerQuotientStructure
import Mathlib.Algebra.Group.Subgroup.Pointwise

namespace OAI

/-! # The integer height on a subgroup generated over a normal kernel -/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (t : G)

abbrev cyclicJoin : Subgroup G := N ⊔ Subgroup.zpowers t

abbrev cyclicJoinLetter : cyclicJoin N t :=
  ⟨t, (show Subgroup.zpowers t ≤ cyclicJoin N t from le_sup_right) (Subgroup.mem_zpowers t)⟩

abbrev quotientLetter : Subgroup.zpowers ((QuotientGroup.mk' N) t) :=
  ⟨(QuotientGroup.mk' N) t, Subgroup.mem_zpowers _⟩

theorem quotientLetter_generates : Subgroup.zpowers (quotientLetter N t) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.property
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩

def cyclicJoinProjection : cyclicJoin N t →* Subgroup.zpowers ((QuotientGroup.mk' N) t) where
  toFun x := ⟨(QuotientGroup.mk' N) x, by
    have h : cyclicJoin N t ≤ (Subgroup.zpowers ((QuotientGroup.mk' N) t)).comap
        (QuotientGroup.mk' N) := by
      apply sup_le
      · intro n hn
        change (QuotientGroup.mk' N) n ∈ Subgroup.zpowers ((QuotientGroup.mk' N) t)
        have hnq : (QuotientGroup.mk' N) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
        rw [hnq]
        exact Subgroup.one_mem _
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_zpowers _)
    exact h x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

variable [Infinite (Subgroup.zpowers ((QuotientGroup.mk' N) t))]

def cyclicJoinHeight : cyclicJoin N t →* Multiplicative ℤ :=
  (intEquivOfZPowersEqTop (quotientLetter N t) (quotientLetter_generates N t)).symm.toMonoidHom.comp
    (cyclicJoinProjection N t)

@[simp] theorem cyclicJoinHeight_letter :
    cyclicJoinHeight N t (cyclicJoinLetter N t) = Multiplicative.ofAdd 1 :=
  intEquivOfZPowersEqTop_symm_self (quotientLetter_generates N t)

theorem cyclicJoinHeight_eq_one_iff (x : cyclicJoin N t) :
    cyclicJoinHeight N t x = 1 ↔ (x : G) ∈ N := by
  let e := intEquivOfZPowersEqTop (quotientLetter N t) (quotientLetter_generates N t)
  change e.symm (cyclicJoinProjection N t x) = 1 ↔ _
  constructor
  · intro hx
    have hp : cyclicJoinProjection N t x = 1 :=
      e.symm.injective (hx.trans e.symm.map_one.symm)
    exact (QuotientGroup.eq_one_iff (x : G)).mp
      (congrArg (fun y : Subgroup.zpowers ((QuotientGroup.mk' N) t) => (y : G ⧸ N)) hp)
  · intro hx
    have hp : cyclicJoinProjection N t x = 1 :=
      Subtype.ext ((QuotientGroup.eq_one_iff (x : G)).mpr hx)
    rw [hp, map_one]

def cyclicJoinHeightKernelEquiv : (cyclicJoinHeight N t).ker ≃* N where
  toFun x := ⟨x.val.val, (cyclicJoinHeight_eq_one_iff N t x.val).mp x.property⟩
  invFun n := ⟨⟨n, (show N ≤ cyclicJoin N t from le_sup_left) n.property⟩,
    (cyclicJoinHeight_eq_one_iff N t _).mpr n.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem cyclicJoinHeightKernelEquiv_conj (x : (cyclicJoinHeight N t).ker) :
    cyclicJoinHeightKernelEquiv N t
      (MulAut.conjNormal (H := (cyclicJoinHeight N t).ker) (cyclicJoinLetter N t) x) =
    MulAut.conjNormal (H := N) t (cyclicJoinHeightKernelEquiv N t x) := by
  apply Subtype.ext
  rfl

end PolycyclicRecognition

end

end OAI
