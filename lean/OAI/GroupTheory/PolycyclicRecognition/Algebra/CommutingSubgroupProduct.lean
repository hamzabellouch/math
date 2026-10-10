import OAI.GroupTheory.PolycyclicRecognition.Algebra.DirectedLowerCentral
import Mathlib.Algebra.Group.Subgroup.Pointwise

namespace OAI

/-! # Products of commuting nilpotent subgroups

Multiplication is a surjective homomorphism from the direct product onto the
join when the two subgroups centralize each other. Nilpotence passes through
this explicit homomorphism.
-/

namespace PolycyclicRecognition

variable {G : Type} [Group G] (H K : Subgroup G)
  (hcomm : ∀ h : H, ∀ k : K, (h : G) * k = (k : G) * h)

def commutingProductHom : H × K →* G where
  toFun p := (p.1 : G) * p.2
  map_one' := one_mul _
  map_mul' p q := by
    change ((p.1 : G) * q.1) * ((p.2 : G) * q.2) =
      ((p.1 : G) * p.2) * ((q.1 : G) * q.2)
    calc
      _ = (p.1 : G) * (((q.1 : G) * p.2) * q.2) := by simp only [mul_assoc]
      _ = (p.1 : G) * (((p.2 : G) * q.1) * q.2) := by rw [hcomm q.1 p.2]
      _ = _ := by simp only [mul_assoc]

theorem commutingProductHom_range : (commutingProductHom H K hcomm).range = H ⊔ K := by
  apply le_antisymm
  · rintro g ⟨⟨h, k⟩, rfl⟩
    exact Subgroup.mul_mem _
      ((show H ≤ H ⊔ K from le_sup_left) h.property)
      ((show K ≤ H ⊔ K from le_sup_right) k.property)
  · apply sup_le
    · intro h hh
      exact ⟨(⟨h, hh⟩, 1), by simp [commutingProductHom]⟩
    · intro k hk
      exact ⟨(1, ⟨k, hk⟩), by simp [commutingProductHom]⟩

include hcomm in
theorem nilpotent_sup_of_commute [Group.IsNilpotent H] [Group.IsNilpotent K] :
    Group.IsNilpotent (H ⊔ K : Subgroup G) := by
  have h := Group.nilpotent_of_surjective (commutingProductHom H K hcomm).rangeRestrict
    (commutingProductHom H K hcomm).rangeRestrict_surjective
  rwa [commutingProductHom_range] at h

end PolycyclicRecognition

end OAI
