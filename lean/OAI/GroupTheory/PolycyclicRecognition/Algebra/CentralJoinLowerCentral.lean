import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Group.Subgroup.Pointwise

namespace OAI

/-! # Adjoining central elements preserves positive lower-central terms -/

namespace PolycyclicRecognition
open scoped commutatorElement Pointwise
variable {G : Type*} [Group G]

theorem commutator_sup_central_right (H K Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) :
    ⁅H, K ⊔ Z⁆ = ⁅H, K⁆ := by
  let : Z.Normal := Z.normal_of_le_center hZ
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro x hx y hy
    have hyp : y ∈ (K : Set G) * (Z : Set G) := by
      rw [← Subgroup.mul_normal]
      exact hy
    obtain ⟨k, hk, z, hz, rfl⟩ := hyp
    have hcomm : ⁅x, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      ((Subgroup.mem_center_iff.mp (hZ hz)) x)
    rw [commutatorElement_mul_right_eq_mul_conj, hcomm]
    simpa only [mul_one, mul_inv_cancel_right] using Subgroup.commutator_mem_commutator hx hk
  · exact Subgroup.commutator_mono le_rfl le_sup_left

theorem commutator_sup_central_left (H K Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) :
    ⁅H ⊔ Z, K⁆ = ⁅H, K⁆ := by
  rw [Subgroup.commutator_comm, commutator_sup_central_right K H Z hZ,
    Subgroup.commutator_comm]

theorem lowerCentralSeries_sup_central (H Z : Subgroup G) (hZ : Z ≤ Subgroup.center G)
    (n : ℕ) : (H ⊔ Z).lowerCentralSeries (n + 1) = H.lowerCentralSeries (n + 1) := by
  induction n with
  | zero =>
    change ⁅H ⊔ Z, H ⊔ Z⁆ = ⁅H, H⁆
    rw [commutator_sup_central_right _ _ Z hZ, commutator_sup_central_left _ _ Z hZ]
  | succ n ih =>
    change ⁅(H ⊔ Z).lowerCentralSeries (n + 1), H ⊔ Z⁆ =
      ⁅H.lowerCentralSeries (n + 1), H⁆
    rw [ih, commutator_sup_central_right _ _ Z hZ]

end PolycyclicRecognition

end OAI
