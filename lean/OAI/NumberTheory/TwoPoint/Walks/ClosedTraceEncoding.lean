import OAI.NumberTheory.TwoPoint.Walks.ColumnClosedEncoding

namespace OAI

/-! The actual closed-pair catalog has length `2*k`, as in the trace bounds. -/

namespace TwoPointCorrelations

open Finset

lemma columnTupleWord_reindex {J R S : ℕ} {P : Fin J → Finset ℕ}
    (he : R = S) (w : ColumnPrimeAssignment J R P)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) :
    columnTupleWord (fun j i => w j (Fin.cast he.symm i))
      (fun i => forward (Fin.cast he.symm i)) (fun i => padding (Fin.cast he.symm i)) =
      columnTupleWord w forward padding := by
  subst S
  rfl

def closedTraceEncoding {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (p : (Fin k → ((j : Fin J) → P j) × (Q × Bool)) ×
      (Fin k → ((j : Fin J) → P j) × (Q × Bool))) :
    (Fin (2 * k) → Bool) × (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) :=
  let castIndex : Fin (2 * k) → Fin (k + k) := Fin.cast (by omega)
  (fun i => closedColumnForward Q p.1 p.2 (castIndex i),
    (fun j i => closedColumnAssignment Q p.1 p.2 j (castIndex i),
      fun i => closedColumnPadding Q p.1 p.2 (castIndex i)))

theorem closedTraceEncoding_word {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (p : (Fin k → ((j : Fin J) → P j) × (Q × Bool)) ×
      (Fin k → ((j : Fin J) → P j) × (Q × Bool))) :
    columnTupleWord (closedTraceEncoding Q p).2.1 (closedTraceEncoding Q p).1
      (fun i => ((closedTraceEncoding Q p).2.2 i).val) =
      integerClosedWordCode Q (fun d => ∏ j, (d j).val) p := by
  dsimp only [closedTraceEncoding]
  exact (columnTupleWord_reindex (show k + k = 2 * k by omega)
    (closedColumnAssignment Q p.1 p.2) (closedColumnForward Q p.1 p.2)
    (fun i => (closedColumnPadding Q p.1 p.2 i).val)).trans
      (closedColumn_encoding_word Q p.1 p.2)

theorem closedTraceEncoding_injective {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Function.Injective (closedTraceEncoding (k := k) (P := P) Q) := by
  intro a b hab
  apply integerClosedWordCode_injective Q _ (primeTuple_injective hprime hdisjoint) k
  rw [← closedTraceEncoding_word Q a, ← closedTraceEncoding_word Q b, hab]

end TwoPointCorrelations

end OAI
