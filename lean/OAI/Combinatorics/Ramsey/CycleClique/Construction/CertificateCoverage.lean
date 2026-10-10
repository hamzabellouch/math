import OAI.Combinatorics.Ramsey.CycleClique.Construction.LayoutCertificate
import OAI.Combinatorics.Ramsey.CycleClique.Construction.Patterns

namespace OAI

/-! Recursive coverage of the canonical pattern domain. Every leaf
is supplied by a separately checked concrete obstruction certificate. -/

namespace CycleClique.Construction
def HasCheckedCertificate (k t : ℕ) (P : List (List ℕ)) : Prop :=
  ∃ (n : ℕ) (c : LayoutCertificate n), c.Check k t P

def amountSequenceForall : ℕ → ℕ → (List ℕ → Prop) → Prop
  | 0, _, F => F []
  | e + 1, b, F => F [] ∧ ∀ q : Fin b,
      amountSequenceForall e (b - (q.val + 1)) (fun p => F ((q.val + 1) :: p))

theorem amountSequenceForall_sound {e b : ℕ} {F : List ℕ → Prop}
    (h : amountSequenceForall e b F) : ∀ p ∈ amountSequences e b, F p := by
  induction e generalizing b F with
  | zero => simpa only [amountSequenceForall, amountSequences, List.mem_singleton, forall_eq] using h
  | succ e ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · obtain ⟨q, hq, hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
      exact ih (h.2 ⟨q, List.mem_range.mp hq⟩) r hr

theorem pathPatterns_forall_zero {b : ℕ} {first : List ℕ}
    {R : List (List ℕ) → Prop} (h : R []) : ∀ P ∈ pathPatterns 0 b first, R P := by
  simpa only [pathPatterns, List.mem_singleton, forall_eq] using h

theorem pathPatterns_forall_step {t b : ℕ} {first : List ℕ} {R : List (List ℕ) → Prop}
    (h : amountSequenceForall t b (fun p =>
      (LexLE first p ∧ LexLE p p.reverse) →
      ∀ P ∈ pathPatterns (t - p.length) (b - p.sum) p, R (p :: P))) :
    ∀ P ∈ pathPatterns (t + 1) b first, R P := by
  intro P hP
  rw [pathPatterns] at hP
  obtain ⟨p, hp, hP⟩ := List.mem_flatMap.mp hP
  obtain ⟨hseq, horder⟩ := List.mem_filter.mp hp
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hP
  exact amountSequenceForall_sound h p hseq (of_decide_eq_true horder) T hT

end CycleClique.Construction

end OAI
