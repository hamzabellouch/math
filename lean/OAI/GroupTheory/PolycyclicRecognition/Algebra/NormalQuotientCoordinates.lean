import Mathlib.GroupTheory.QuotientGroup.Basic

namespace OAI

/-! # Coset coordinates for induction from a normal subgroup -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def normalQuotientRepresentative (c : G ⧸ N) : G :=
  (QuotientGroup.mk'_surjective N c).choose

@[simp] theorem normalQuotientRepresentative_mk (c : G ⧸ N) :
    QuotientGroup.mk' N (normalQuotientRepresentative N c) = c :=
  (QuotientGroup.mk'_surjective N c).choose_spec

@[simp] theorem normalQuotient_mk_subgroup (n : N) :
    QuotientGroup.mk' N (n : G) = 1 :=
  (QuotientGroup.eq_one_iff (n : G)).mpr n.property

def normalQuotientPart (g : G) : N :=
  ⟨g * (normalQuotientRepresentative N (QuotientGroup.mk' N g))⁻¹, by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N
      (g * (normalQuotientRepresentative N (QuotientGroup.mk' N g))⁻¹) = 1
    rw [map_mul, map_inv, normalQuotientRepresentative_mk, mul_inv_cancel]⟩

@[simp] theorem normalQuotientPart_mul (n : N) (g : G) :
    normalQuotientPart N ((n : G) * g) = n * normalQuotientPart N g := by
  apply Subtype.ext
  change ((n : G) * g) *
      (normalQuotientRepresentative N (QuotientGroup.mk' N ((n : G) * g)))⁻¹ =
    (n : G) * (g * (normalQuotientRepresentative N (QuotientGroup.mk' N g))⁻¹)
  rw [map_mul, normalQuotient_mk_subgroup, one_mul, mul_assoc]

@[simp] theorem normalQuotientPart_representative (c : G ⧸ N) :
    normalQuotientPart N (normalQuotientRepresentative N c) = 1 := by
  apply Subtype.ext
  change normalQuotientRepresentative N c *
    (normalQuotientRepresentative N
      (QuotientGroup.mk' N (normalQuotientRepresentative N c)))⁻¹ = 1
  rw [normalQuotientRepresentative_mk, mul_inv_cancel]

theorem normalQuotientPart_decompose (g : G) :
    (normalQuotientPart N g : G) *
      normalQuotientRepresentative N (QuotientGroup.mk' N g) = g := by
  simp [normalQuotientPart, mul_assoc]

end PolycyclicRecognition

end

end OAI
