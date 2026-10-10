import OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.FibreWeightSeparation

theorem positive_indices {m : ℕ} (w cost : Fin (m+1) → ℝ) (C : ℝ)
    (hsep : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      C * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j) :
    ∀ A B : Finset (Fin m), A.card = B.card →
      ∀ i, i ∈ A → i ∉ B → (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      C * (∏ j ∈ B, cost j.succ) < ∏ j ∈ A, w j.succ := by
  intro A B hcard i hiA hiB hlarge
  have h := hsep (A.map (Fin.succEmb m)) (B.map (Fin.succEmb m))
    (by simpa only [Finset.card_map] using hcard) i.succ (Fin.succ_ne_zero i)
    (by simpa using hiA) (by simpa using hiB) (by
      intro j hij
      cases j using Fin.cases with
      | zero => exact (not_lt_of_ge (Fin.zero_le _) hij).elim
      | succ j => simpa using hlarge j (Fin.succ_lt_succ_iff.mp hij))
  simpa only [Finset.prod_map, Fin.coe_succEmb] using h

end PiExponent.FibreWeightSeparation
end

end OAI
