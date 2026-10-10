import OAI.Probability.SATComputability.RelaxedCandidates
import OAI.Probability.SATComputability.VariableDeletion

namespace OAI

namespace FixedClauseThreshold.Computability

open Finset
open scoped Classical

def encodeDeletion {n : ℕ} (D : Finset (Fin n)) (s : Fin n → Bool) : DeletionCandidate n :=
  fun v => if v ∈ D then none else some (s v)

def deletedVariables {n : ℕ} (x : DeletionCandidate n) : Finset (Fin n) :=
  univ.filter (fun v => x v = none)

theorem literalFalse_encode {n : ℕ} (D : Finset (Fin n)) (s : Fin n → Bool)
    (v : Fin n) (b : Bool) :
    ¬literalFalse (encodeDeletion D s) (v, b) ↔ v ∈ D ∨ s v = b := by
  by_cases hv : v ∈ D
  · simp [literalFalse, encodeDeletion, hv]
  · cases hb : s v <;> cases b <;> simp [literalFalse, encodeDeletion, hv, hb]

theorem deletedVariables_encode {n : ℕ} (D : Finset (Fin n)) (s : Fin n → Bool) :
    deletedVariables (encodeDeletion D s) = D := by
  ext v
  by_cases hv : v ∈ D <;> simp [deletedVariables, encodeDeletion, hv]

theorem deletionSatisfiable_iff_candidate {n m r : ℕ}
    (indices : Fin m → Fin 3 → Fin n) (signs : Fin m → Fin 3 → Bool) :
    deletionSatisfiable r indices signs ↔
      ∃ x : DeletionCandidate n, (deletedVariables x).card ≤ r ∧
        ∀ j, ∃ l, ¬literalFalse x (indices j l, signs j l) := by
  constructor
  · rintro ⟨D, hD, s, hs⟩
    refine ⟨encodeDeletion D s, ?_, ?_⟩
    · simpa only [deletedVariables_encode] using hD
    · intro j
      rcases hs j with ⟨l, hl⟩ | ⟨l, hl⟩
      · exact ⟨l, (literalFalse_encode D s _ _).mpr (Or.inl hl)⟩
      · exact ⟨l, (literalFalse_encode D s _ _).mpr (Or.inr hl)⟩
  · rintro ⟨x, hx, hs⟩
    let D := deletedVariables x
    let s : Fin n → Bool := fun v => (x v).getD false
    refine ⟨D, hx, s, ?_⟩
    intro j
    obtain ⟨l, hl⟩ := hs j
    cases hv : x (indices j l) with
    | none =>
        left
        exact ⟨l, by simp [D, deletedVariables, hv]⟩
    | some b =>
        right
        refine ⟨l, ?_⟩
        have hb : b = signs j l := by
          cases b <;> cases hsign : signs j l <;>
            simp_all [literalFalse]
        simpa only [s, hv, Option.getD_some] using hb

end FixedClauseThreshold.Computability

end OAI
