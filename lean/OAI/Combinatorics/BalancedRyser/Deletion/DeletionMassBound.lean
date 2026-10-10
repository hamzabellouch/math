import OAI.Combinatorics.BalancedRyser.Deletion.DeletionAssignments
import OAI.Combinatorics.BalancedRyser.Deletion.DeletionDomination

namespace OAI

open scoped BigOperators

namespace Balanced.DeletionLaw

def outputRoles {q n : ℕ} (ω : Offset q n × Split q n) : Fin n → Fin 3 → Fin q :=
  fun i => ![ω.1 i, ω.2 0 i, ω.2 1 i]

 theorem outputRoles_injective {q n : ℕ} :
    Function.Injective (@outputRoles q n) := by
  intro a b hab
  apply Prod.ext
  · funext i
    simpa [outputRoles] using congrFun (congrFun hab i) (0 : Fin 3)
  · funext j i
    fin_cases j
    · simpa [outputRoles] using congrFun (congrFun hab i) (1 : Fin 3)
    · simpa [outputRoles] using congrFun (congrFun hab i) (2 : Fin 3)

 theorem outputRoles_image {q n : ℕ} (ω : Offset q n × Split q n) (i : Fin n) :
    Finset.univ.image (outputRoles ω i) = deletionSet ω.1 ω.2 i := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, deletionSet,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨j, hj⟩
    fin_cases j <;> simp_all [outputRoles]
  · rintro (h | h | h)
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩

theorem deletionMass_le_of_offsetAverage_le {q n : ℕ}
    (κ : Weight q n) (hκ : ∀ m₀ m₁ s, 0 ≤ κ m₀ m₁ s)
    (D : DeletionSet q n) (hD : ∀ i, (D i).card = 3)
    (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ m₁ s, offsetAverage κ m₁ s ≤ c) :
    deletionMass κ D ≤ (6 : ℝ) ^ n * c := by
  classical
  have hw : ∀ ω : Offset q n × Split q n, 0 ≤ offsetAverage κ ω.1 ω.2 := by
    intro ω
    exact div_nonneg (Finset.sum_nonneg (fun m₀ _ => hκ m₀ ω.1 ω.2))
      (pow_nonneg (Nat.cast_nonneg q) _)
  have hd := DeletionAssignments.weighted_unordered_deletion_le_of_injective_roles
    (fun ω : Offset q n × Split q n => offsetAverage κ ω.1 ω.2) hw
    outputRoles outputRoles_injective D hD c hc (fun ω => hbound ω.1 ω.2)
  simpa only [outputRoles_image, ← funext_iff, Fintype.card_fin,
    Fintype.sum_prod_type, deletionMass] using hd

end Balanced.DeletionLaw

end OAI
