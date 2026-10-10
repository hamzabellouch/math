import Mathlib.GroupTheory.Nilpotent

namespace OAI

/-! # Iterated differences of an automorphism induced by nilpotent conjugation

No commutativity of the invariant subgroup is required. Each successive
difference lies one step deeper in the lower central series of the ambient
group.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G H : Type*} [Group G] [Group H]

theorem conjugation_difference_iterate_mem (t x : G) (n : ℕ) :
    (fun y => t * y * t⁻¹ * y⁻¹)^[n] x ∈
      (⊤ : Subgroup G).lowerCentralSeries n := by
  induction n with
  | zero => exact Subgroup.mem_top _
  | succ n ih =>
    rw [Function.iterate_succ_apply', Subgroup.lowerCentralSeries_succ,
      Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top t) ih

theorem conjugation_difference_iterate_one [Group.IsNilpotent G] (t x : G) :
    (fun y => t * y * t⁻¹ * y⁻¹)^[Group.nilpotencyClass G] x = 1 := by
  have h := conjugation_difference_iterate_mem t x (Group.nilpotencyClass G)
  rwa [Subgroup.lowerCentralSeries_nilpotencyClass, Subgroup.mem_bot] at h

theorem automorphism_difference_iterate_map (j : H →* G) (A : H ≃* H) (t : G)
    (hA : ∀ x, j (A x) = t * j x * t⁻¹) (n : ℕ) (x : H) :
    j ((fun y => A y * y⁻¹)^[n] x) =
      (fun y => t * y * t⁻¹ * y⁻¹)^[n] (j x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_mul,
      map_inv, hA, ih]

theorem automorphism_difference_iterate_one [Group.IsNilpotent G]
    (j : H →* G) (hj : Function.Injective j) (A : H ≃* H) (t : G)
    (hA : ∀ x, j (A x) = t * j x * t⁻¹) (x : H) :
    (fun y => A y * y⁻¹)^[Group.nilpotencyClass G] x = 1 := by
  apply hj
  rw [map_one, automorphism_difference_iterate_map j A t hA,
    conjugation_difference_iterate_one]

end PolycyclicRecognition

end

end OAI
