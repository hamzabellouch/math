import Mathlib
import OAI.Computability.Interspersed.Execution

namespace OAI

/-! Blank tails and finite storage bounds for interspersed histories. -/

noncomputable section
open scoped ContDiff
namespace PrefixFlows
namespace Interspersed
variable {Q A : Type*} {H : Set Q}
def BlankAfter {B : Type*} (b : B) (n : ℕ) (L : Stack B) : Prop :=
  ∀ k, n ≤ k → L k = b

theorem blankAfter_mono {B : Type*} {b : B} {n m : ℕ} {L : Stack B}
    (h : BlankAfter b n L) (hnm : n ≤ m) : BlankAfter b m L :=
  fun k hk => h k (hnm.trans hk)

theorem blankAfter_push {B : Type*} {a b : B} {n : ℕ} {L : Stack B}
    (h : BlankAfter b n L) : BlankAfter b (n + 1) (push a L) := by
  intro k hk
  cases k with
  | zero => omega
  | succ k => exact h k (by omega)

theorem blankAfter_of_push {B : Type*} {a b : B} {n : ℕ} {L : Stack B}
    (h : BlankAfter b n (push a L)) : BlankAfter b n L := by
  intro k hk
  exact h (k + 1) (by omega)

theorem blankAfter_prepend {B : Type*} {b : B} {n : ℕ} {L : Stack B}
    (w : List B) (h : BlankAfter b n L) : BlankAfter b (w.length + n) (prepend w L) := by
  induction w with
  | nil => simpa using h
  | cons a w ih => simpa [Nat.add_right_comm] using (blankAfter_push (a := a) ih)

theorem blankAfter_const {B : Type*} (b : B) : BlankAfter b 0 (fun _ => b) :=
  fun _ _ => rfl

def BlankConfiguration (b : A) (n : ℕ) (c : Config Q A H) : Prop :=
  BlankAfter (.inl b) n c.2.1 ∧ BlankAfter (.inl b) n c.2.2

theorem source_tails_blank (b : A) (n : ℕ) (r : Branch Q A H)
    (L R : Stack (Symbol Q A H)) (h : BlankConfiguration b n (source r L R)) :
    BlankAfter (.inl b) n L ∧ BlankAfter (.inl b) n R := by
  cases r with
  | main q h' a => exact ⟨h.1, blankAfter_of_push h.2⟩
  | rightRecord q g => exact ⟨h.1, blankAfter_of_push h.2⟩
  | rightWork q a => exact ⟨h.1, blankAfter_of_push h.2⟩
  | leftRecord q g => exact ⟨blankAfter_of_push h.1, h.2⟩
  | leftWork q a => exact ⟨blankAfter_of_push h.1, h.2⟩

theorem target_tails_blank (δ : Q → A → Q × A × Move) (b : A) (n : ℕ)
    (r : Branch Q A H) (L R : Stack (Symbol Q A H))
    (h : BlankAfter (.inl b) n L ∧ BlankAfter (.inl b) n R) :
    BlankConfiguration b (n + 2) (target δ r L R) := by
  have h0 {S : Stack (Symbol Q A H)} (hs : BlankAfter (.inl b) n S) :
      BlankAfter (.inl b) (n + 2) S := blankAfter_mono hs (by omega)
  have h1 {S : Stack (Symbol Q A H)} (a : Symbol Q A H) (hs : BlankAfter (.inl b) n S) :
      BlankAfter (.inl b) (n + 2) (push a S) :=
    blankAfter_mono (blankAfter_push hs) (by omega)
  have h2 {S : Stack (Symbol Q A H)} (a c : Symbol Q A H)
      (hs : BlankAfter (.inl b) n S) :
      BlankAfter (.inl b) (n + 2) (push a (push c S)) :=
    blankAfter_push (blankAfter_push hs)
  cases r <;> simp only [target]
  all_goals (repeat' split)
  all_goals constructor
  all_goals first | exact h0 h.1 | exact h0 h.2 |
    exact h1 _ h.1 | exact h1 _ h.2 | exact h2 _ _ h.1 | exact h2 _ _ h.2

theorem Step.preserves_blank {δ : Q → A → Q × A × Move}
    {b : A} {n : ℕ} {c d : Config Q A H} (h : Step δ c d)
    (hc : BlankConfiguration b n c) : BlankConfiguration b (n + 2) d := by
  rcases h with ⟨r, L, R, rfl, rfl⟩
  exact target_tails_blank δ b n r L R (source_tails_blank b n r L R hc)

 

theorem Exec.preserves_blank {δ : Q → A → Q × A × Move}
    {b : A} {n k : ℕ} {c d : Config Q A H} (h : Exec δ k c d)
    (hc : BlankConfiguration b n c) : BlankConfiguration b (n + 2 * k) d := by
  induction h generalizing n with
  | zero c => simpa using hc
  | succ hs he ih =>
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using ih (hs.preserves_blank hc)

 

theorem initialized_storage_bound (δ : Q → A → Q × A × Move) (b : A)
    (q : Q) (w : List A) {k : ℕ} {c : Config Q A H}
    (h : Exec δ k (.main q .stay, (fun _ => .inl b),
      prepend (w.map Sum.inl) (fun _ => .inl b)) c) :
    BlankConfiguration b (w.length + 2 * k) c := by
  apply h.preserves_blank
  constructor
  · exact blankAfter_mono (blankAfter_const (Sum.inl b : Symbol Q A H)) (Nat.zero_le _)
  · simpa using blankAfter_prepend (w.map Sum.inl) (blankAfter_const (Sum.inl b : Symbol Q A H))

theorem stack_eta {B : Type*} (L : Stack B) :
    push (L 0) (fun k => L (k + 1)) = L := by
  funext k
  cases k <;> rfl

 

theorem split_at_work {G : Type*} (b : A) {n : ℕ} {L : Stack (A ⊕ G)}
    (h : BlankAfter (.inl b) n L) :
    ∃ (gs : List G) (a : A) (R : Stack (A ⊕ G)),
      gs.length ≤ n ∧ L = prepend (gs.map Sum.inr) (push (.inl a) R) := by
  induction n generalizing L with
  | zero =>
    refine ⟨[], b, (fun k => L (k + 1)), by simp, ?_⟩
    have he := (stack_eta L).symm
    rw [h 0 (by omega)] at he
    exact he
  | succ n ih =>
    have ht : BlankAfter (.inl b) n (fun k => L (k + 1)) :=
      fun k hk => h (k + 1) (by omega)
    have he := (stack_eta L).symm
    cases h0 : L 0 with
    | inl a =>
      refine ⟨[], a, (fun k => L (k + 1)), Nat.zero_le _, ?_⟩
      simpa only [h0, List.map_nil, prepend_nil] using he
    | inr g =>
      rcases ih ht with ⟨gs, a, R, hn, hr⟩
      refine ⟨g :: gs, a, R, by simpa using Nat.succ_le_succ hn, ?_⟩
      rw [h0, hr] at he
      exact he
end Interspersed
end PrefixFlows
end

end OAI
