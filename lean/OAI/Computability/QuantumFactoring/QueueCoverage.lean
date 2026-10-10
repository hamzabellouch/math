import Mathlib
import OAI.Computability.QuantumFactoring.OccurrenceQueue

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.AuxiliaryTree

/-- Chronological node heads, in reverse recording order. Zero denotes a dummy
slot after the pending queue has become empty. Duplicate occurrences remain. -/
def seen (xs : List ℕ) : ℕ→List ℕ
  | 0=>[]
  | t+1=>(run t xs).headD 0::seen xs t

lemma head_or_advance {xs : List ℕ} {a : ℕ} (ha : a∈xs) :
    a=xs.headD 0 ∨ a∈advance xs := by
  cases xs with
  | nil=>simp at ha
  | cons b bs=>
    rcases List.mem_cons.mp ha with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_append_right _ h)
lemma children_head (xs : List ℕ) {a : ℕ} (ha : a∈children (xs.headD 0)) : a∈advance xs := by
  cases xs with
  | nil=>simp [children] at ha
  | cons b bs=>exact List.mem_append_left _ ha

/-- Everything pending before a step is either the recorded head or remains
pending afterwards. This assertion does not search the mathematical tree. -/
lemma seen_or_pending_step {xs : List ℕ} {t a : ℕ}
    (h : a∈seen xs t ∨ a∈run t xs) : a∈seen xs (t+1) ∨ a∈run (t+1) xs := by
  rcases h with h | h
  · exact Or.inl (List.mem_cons_of_mem _ h)
  · rcases head_or_advance h with h | h
    · exact Or.inl (List.mem_cons.mpr (Or.inl h))
    · exact Or.inr (by rw [run_succ_right];exact h)

lemma original_covered (xs : List ℕ) (t : ℕ) {a : ℕ} (ha : a∈xs) :
    a∈seen xs t ∨ a∈run t xs := by
  induction t with
  | zero=>exact Or.inr ha
  | succ t ih=>exact seen_or_pending_step ih

/-- Every required p−1 child of every already visited node is itself either
visited or still on the actual occurrence queue. -/
lemma children_covered (xs : List ℕ) (t : ℕ) {m a : ℕ}
    (hm : m∈seen xs t) (ha : a∈children m) : a∈seen xs t ∨ a∈run t xs := by
  induction t with
  | zero=>simp [seen] at hm
  | succ t ih=>
    rcases List.mem_cons.mp hm with hm | hm
    · have hx : a∈advance (run t xs) := children_head _ (by simpa only [←hm] using ha)
      exact Or.inr (by rw [run_succ_right];exact hx)
    · exact seen_or_pending_step (ih hm)

lemma completed_root {m n : ℕ} (hm : 2 ≤ m) (hb : m < 2^n) : m∈seen [m] (2*n^2) := by
  have h:=original_covered [m] (2*n^2) (by simp : m∈[m])
  rw [run_complete hm hb] at h
  simpa only [List.not_mem_nil,or_false] using h
lemma completed_children {m n a b : ℕ} (hm : 2 ≤ m) (hb : m < 2^n)
    (ha : a∈seen [m] (2*n^2)) (hc : b∈children a) : b∈seen [m] (2*n^2) := by
  have h:=children_covered [m] (2*n^2) ha hc
  rw [run_complete hm hb] at h
  simpa only [List.not_mem_nil,or_false] using h
lemma seen_length (xs : List ℕ) (t : ℕ) : (seen xs t).length=t := by
  induction t with
  | zero=>rfl
  | succ t ih=>simp only [seen,List.length_cons,ih]
end ExactQuantumFactoring.AuxiliaryTree


end

end OAI
