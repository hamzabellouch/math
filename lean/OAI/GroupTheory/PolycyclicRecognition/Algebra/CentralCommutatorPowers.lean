import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Commute.Basic

namespace OAI

/-! # Integral collection formulas for a central commutator

These are the integer-power formulas needed to collect lattice coordinates.
-/

namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type*} [Group G] {a b : G}

theorem central_commutator_zpow_left (h : ⁅a, b⁆ ∈ Subgroup.center G) (n : ℤ) :
    ⁅a ^ n, b⁆ = ⁅a, b⁆ ^ n := by
  have hc : Commute a ⁅a, b⁆ := (Subgroup.mem_center_iff.mp h a)
  cases n with
  | ofNat k => simpa using (hc.commutatorElement_pow_left k).symm
  | negSucc k =>
    rw [zpow_negSucc, zpow_negSucc, commutatorElement_inv_left,
      ← commutatorElement_inv, ← hc.commutatorElement_pow_left (k + 1)]
    have hp : Commute (a ^ (k + 1)) (⁅a, b⁆ ^ (k + 1)) := hc.pow_pow _ _
    exact hp.inv_right.inv_mul_cancel

theorem central_commutator_zpow_right (h : ⁅a, b⁆ ∈ Subgroup.center G) (n : ℤ) :
    ⁅a, b ^ n⁆ = ⁅a, b⁆ ^ n := by
  have hb : ⁅b, a⁆ ∈ Subgroup.center G := by
    rw [← commutatorElement_inv]
    exact (Subgroup.center G).inv_mem h
  calc
    ⁅a, b ^ n⁆ = ⁅b ^ n, a⁆⁻¹ := (commutatorElement_inv _ _).symm
    _ = (⁅b, a⁆ ^ n)⁻¹ := congrArg Inv.inv (central_commutator_zpow_left hb n)
    _ = ⁅a, b⁆ ^ n := by rw [← commutatorElement_inv, inv_zpow, inv_inv]

theorem central_commutator_zpow (h : ⁅a, b⁆ ∈ Subgroup.center G) (m n : ℤ) :
    ⁅a ^ m, b ^ n⁆ = ⁅a, b⁆ ^ (m * n) := by
  have hm : ⁅a ^ m, b⁆ ∈ Subgroup.center G := by
    rw [central_commutator_zpow_left h]
    exact (Subgroup.center G).zpow_mem h m
  rw [central_commutator_zpow_right hm, central_commutator_zpow_left h, ← zpow_mul]

theorem central_zpow_collection (h : ⁅a, b⁆ ∈ Subgroup.center G) (m n : ℤ) :
    a ^ m * b ^ n = ⁅a, b⁆ ^ (m * n) * b ^ n * a ^ m := by
  rw [← central_commutator_zpow h m n, commutatorElement_def]
  simp [mul_assoc]

end PolycyclicRecognition

end OAI
