import OAI.Probability.SATComputability.SATModel

namespace OAI

namespace FixedClauseThreshold.Computability

open Finset

def relaxedClauseSatisfied {n : ℕ} (s : Fin n → Bool)
    (indices : Fin 3 → Fin n) (signs : Fin 3 → Bool) : Prop :=
  ∃ l, s (indices l) = signs l

instance {n : ℕ} (s : Fin n → Bool) (indices : Fin 3 → Fin n)
    (signs : Fin 3 → Bool) : Decidable (relaxedClauseSatisfied s indices signs) := by
  unfold relaxedClauseSatisfied
  infer_instance

def relaxedViolations {n m : ℕ} (s : Fin n → Bool)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) : ℕ :=
  (univ.filter fun j => ¬relaxedClauseSatisfied s (indices j) (signs j)).card

def deletionSatisfiable {n m : ℕ} (r : ℕ)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) : Prop :=
  ∃ D : Finset (Fin n), D.card ≤ r ∧ ∃ s : Fin n → Bool,
    ∀ j, (∃ l, indices j l ∈ D) ∨ relaxedClauseSatisfied s (indices j) (signs j)

theorem delete_one_per_violation {n m : ℕ} (s : Fin n → Bool)
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) :
    deletionSatisfiable (relaxedViolations s indices signs) indices signs := by
  let bad := univ.filter fun j => ¬relaxedClauseSatisfied s (indices j) (signs j)
  refine ⟨bad.image (fun j => indices j 0), Finset.card_image_le, s, ?_⟩
  intro j
  by_cases h : relaxedClauseSatisfied s (indices j) (signs j)
  · exact Or.inr h
  · left
    refine ⟨0, Finset.mem_image.mpr ⟨j, ?_, rfl⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩

theorem deletionSatisfiable_mono {n m r t : ℕ} (hrt : r ≤ t)
    {indices : Fin m → Fin 3 → Fin n} {signs : Fin m → Fin 3 → Bool}
    (h : deletionSatisfiable r indices signs) : deletionSatisfiable t indices signs := by
  obtain ⟨D, hD, s, hs⟩ := h
  exact ⟨D, hD.trans hrt, s, hs⟩

theorem violations_gt_of_deletion_unsat {n m r : ℕ}
    {indices : Fin m → Fin 3 → Fin n} {signs : Fin m → Fin 3 → Bool}
    (h : ¬deletionSatisfiable r indices signs) (s : Fin n → Bool) :
    r < relaxedViolations s indices signs := by
  by_contra! hle
  exact h (deletionSatisfiable_mono hle (delete_one_per_violation s indices signs))

end FixedClauseThreshold.Computability

end OAI
