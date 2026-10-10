import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralCommutatorPowers
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Module.Equiv.Basic

namespace OAI

/-! # The actual central commutator pairing

For a group of class at most two, the commutator is a bilinear alternating
map on its abelianization. The target here is the actual center, not a
formal copy of the abelianization. This is the first central-layer map
needed in the nilpotent homology argument.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement IsMulCommutative
variable {G : Type} [Group G]

theorem commutator_mul_left_of_central (a b c : G)
    (hb : ⁅b, c⁆ ∈ Subgroup.center G) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  have hc : Commute a ⁅b, c⁆ := Subgroup.mem_center_iff.mp hb a
  rw [commutatorElement_mul_left_eq_conj_mul, hc.eq, mul_inv_cancel_right]
  exact (Subgroup.mem_center_iff.mp hb ⁅a, c⁆).symm

theorem commutator_mul_right_of_central (a b c : G)
    (hc : ⁅a, c⁆ ∈ Subgroup.center G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have hb : Commute b ⁅a, c⁆ := Subgroup.mem_center_iff.mp hc b
  rw [commutatorElement_mul_right_eq_mul_conj, hb.right_comm, mul_inv_cancel_right]

theorem central_commutator_mul_left
    (h : commutator G ≤ Subgroup.center G) (a b c : G) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  have hb : ⁅b, c⁆ ∈ Subgroup.center G :=
    h (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  exact commutator_mul_left_of_central a b c hb

theorem central_commutator_mul_right
    (h : commutator G ≤ Subgroup.center G) (a b c : G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have hc : ⁅a, c⁆ ∈ Subgroup.center G :=
    h (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  exact commutator_mul_right_of_central a b c hc

def centerCommutatorLeft (h : commutator G ≤ Subgroup.center G) (b : G) :
    G →* Subgroup.center G where
  toFun a := ⟨⁅a, b⁆, h (Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) (Subgroup.mem_top _))⟩
  map_one' := Subtype.ext (commutatorElement_one_left b)
  map_mul' a c := Subtype.ext (central_commutator_mul_left h a c b)

def centerCommutatorRight (h : commutator G ≤ Subgroup.center G)
    (a : Abelianization G) : G →* Subgroup.center G where
  toFun b := Abelianization.lift (centerCommutatorLeft h b) a
  map_one' := by
    induction a using QuotientGroup.induction_on with | H a =>
      exact Subtype.ext (commutatorElement_one_right a)
  map_mul' b c := by
    induction a using QuotientGroup.induction_on with | H a =>
      exact Subtype.ext (central_commutator_mul_right h a b c)

def centerCommutatorPairing (h : commutator G ≤ Subgroup.center G) :
    Additive (Abelianization G) →ₗ[ℤ]
      Additive (Abelianization G) →ₗ[ℤ] Additive (Subgroup.center G) where
  toFun a := (Abelianization.lift (centerCommutatorRight h a.toMul)).toAdditive.toIntLinearMap
  map_add' a b := by
    apply LinearMap.ext
    intro c
    induction c using QuotientGroup.induction_on with | H c =>
      change Additive.ofMul (Abelianization.lift (centerCommutatorLeft h c)
        (a.toMul * b.toMul)) = _
      exact congrArg Additive.ofMul (map_mul (Abelianization.lift
        (centerCommutatorLeft h c)) a.toMul b.toMul)
  map_smul' n a := by
    apply LinearMap.ext
    intro c
    induction c using QuotientGroup.induction_on with | H c =>
      change Additive.ofMul (Abelianization.lift (centerCommutatorLeft h c)
        (a.toMul ^ n)) = _
      exact congrArg Additive.ofMul (map_zpow (Abelianization.lift
        (centerCommutatorLeft h c)) a.toMul n)

@[simp] theorem centerCommutatorPairing_of
    (h : commutator G ≤ Subgroup.center G) (a b : G) :
    centerCommutatorPairing h (Additive.ofMul (Abelianization.of a))
      (Additive.ofMul (Abelianization.of b)) =
      Additive.ofMul ⟨⁅a, b⁆, h (Subgroup.commutator_mem_commutator
        (Subgroup.mem_top _) (Subgroup.mem_top _))⟩ := rfl

theorem centerCommutatorPairing_self
    (h : commutator G ≤ Subgroup.center G) (a : Additive (Abelianization G)) :
    centerCommutatorPairing h a a = 0 := by
  induction a using QuotientGroup.induction_on with | H a =>
    exact congrArg Additive.ofMul (Subtype.ext (commutatorElement_self a))

end PolycyclicRecognition

end

end OAI
