import Mathlib
import OAI.Computability.QuantumFactoring.BitStackPrograms

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

variable {K L : Type}
def Program.relabel (f : K → L) : Program K → Program L
  | .skip => .skip
  | .push k b => .push (f k) b
  | .seq p q => .seq (p.relabel f) (q.relabel f)
  | .cases k p q r => .cases (f k) (p.relabel f) (q.relabel f) (r.relabel f)
  | .loop k p q => .loop (f k) (p.relabel f) (q.relabel f)

/-- An extension of a small register store with arbitrary untouched registers. -/
noncomputable def overlay (f : K ↪ L) (base : Store L) (s : Store K) : Store L := by
  classical
  exact fun j => if h : ∃ i, f i=j then s (Classical.choose h) else base j

lemma overlay_at (f : K ↪ L) (base : Store L) (s : Store K) (i : K) :
    overlay f base s (f i)=s i := by
  classical
  unfold overlay
  rw [dite_eq_left ⟨i,rfl⟩]
  congr 1
  apply f.injective
  exact Classical.choose_spec (show ∃ k, f k=f i from ⟨i,rfl⟩)

lemma overlay_outside (f : K ↪ L) (base : Store L) (s : Store K) (j : L)
    (h : ∀ i, f i≠j) : overlay f base s j=base j := by
  classical
  unfold overlay
  exact dite_eq_right (by simpa only [not_exists] using h)

variable [DecidableEq K] [DecidableEq L]

lemma overlay_update (f : K ↪ L) (base : Store L) (s : Store K) (k : K) (xs : List Bool) :
    overlay f base (Function.update s k xs)=Function.update (overlay f base s) (f k) xs := by
  funext j
  by_cases hj : ∃ i,f i=j
  · rcases hj with ⟨i,rfl⟩
    rw [overlay_at]
    by_cases h : i=k
    · subst i; simp
    · have hf : f i≠f k := fun h' => h (f.injective h')
      simp only [Function.update_of_ne h,Function.update_of_ne hf,overlay_at]
  · have h : ∀ i,f i≠j := by simpa only [not_exists] using hj
    rw [overlay_outside f base _ j h,Function.update_of_ne (Ne.symm (h k)),
      overlay_outside f base s j h]

omit [DecidableEq K] [DecidableEq L] in
lemma overlay_self (f : K ↪ L) (s : Store L) : overlay f s (s ∘ f)=s := by
  funext j
  by_cases h : ∃ i,f i=j
  · rcases h with ⟨i,rfl⟩
    exact overlay_at f s (s ∘ f) i
  · exact overlay_outside f s (s ∘ f) j (by simpa only [not_exists] using h)

/-- Exact-cost subroutine embedding. Scratch separation is proved, not assumed
as an extra TM operation. -/
lemma Runs.relabel {p : Program K} {s t : Store K} {c : ℕ}
    (h : Runs p s t c) (f : K ↪ L) (base : Store L) :
    Runs (p.relabel f) (overlay f base s) (overlay f base t) c := by
  induction h with
  | skip s => exact Runs.skip _
  | push s k b =>
    rw [overlay_update]
    simpa only [overlay_at, Program.relabel] using Runs.push (overlay f base s) (f k) b
  | seq hp hq ip iq => exact Runs.seq ip iq
  | @cases_nil k p q r s t a hs hr ih =>
    exact Runs.cases_nil (by rw [overlay_at,hs]) ih
  | @cases_false k p q r s t xs a hs hr ih =>
    rw [overlay_update] at ih
    exact Runs.cases_false (by rw [overlay_at,hs]) ih
  | @cases_true k p q r s t xs a hs hr ih =>
    rw [overlay_update] at ih
    exact Runs.cases_true (by rw [overlay_at,hs]) ih
  | @loop_nil k p q s hs => exact Runs.loop_nil (by rw [overlay_at,hs])
  | @loop_false k p q s t u xs a b hs hp hq ip iq =>
    rw [overlay_update] at ip
    exact Runs.loop_false (by rw [overlay_at,hs]) ip iq
  | @loop_true k p q s t u xs a b hs hp hq ip iq =>
    rw [overlay_update] at ip
    exact Runs.loop_true (by rw [overlay_at,hs]) ip iq
end ExactQuantumFactoring.BitStackProgram

end


end OAI
