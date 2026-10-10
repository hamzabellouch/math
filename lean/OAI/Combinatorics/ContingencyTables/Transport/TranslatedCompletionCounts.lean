import OAI.Combinatorics.ContingencyTables.Transport.TranslatedCompletions

namespace OAI

/-! # Symmetric accepted counts for the literal completion adjustment -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators Classical

variable {X I J : Type*} [Fintype I] [Fintype J]

noncomputable def blockCount (R : X → Option I → ℕ) (P : X → Option J → ℕ) (x : X) : ℕ :=
  Fintype.card (Table (R x) (P x))

noncomputable def acceptedCount (R : X → Option I → ℕ) (P : X → Option J → ℕ) (x y : X) : ℕ :=
  Fintype.card (Accepted (R x) (P x) (between (R x) (R y) (P x) (P y)))

lemma blockCount_pos (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j) (x : X) : 0 < blockCount R P x :=
  Fintype.card_pos_iff.mpr (table_nonempty (R x) (P x) (htotal x))

lemma acceptedCount_le (R : X → Option I → ℕ) (P : X → Option J → ℕ) (x y : X) :
    acceptedCount R P x y ≤ blockCount R P x :=
  Fintype.card_subtype_le _

/-- Reversibility uses the cardinality of actual accepted translations,
not a Metropolis weight-ratio oracle. -/
theorem acceptedCount_symmetric (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (htotal : ∀ x,(∑ i,R x i)=∑ j,P x j) (x y : X) :
    acceptedCount R P x y=acceptedCount R P y x := by
  have he := accepted_card_symmetric (R x) (R y) (P x) (P y)
    (between (R x) (R y) (P x) (P y))
    (between_rows (R x) (R y) (P x) (P y))
    (between_columns (R x) (R y) (P x) (P y) (htotal x) (htotal y))
  unfold acceptedCount
  rw [between_reverse (R x) (R y) (P x) (P y)]
  exact he

end ContingencyTables.CompletionTranslation

end OAI
