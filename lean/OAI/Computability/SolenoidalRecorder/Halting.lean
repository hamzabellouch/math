import Mathlib
import OAI.Computability.SolenoidalRecorder.Checkpoints

namespace OAI

/-! Terminal recorder checkpoints and initialized halting equivalence. -/

namespace Solenoidal
namespace Recorder
variable {M : Machine}
def Terminal (c : Config M) : Prop := ∃ q : M.State, c.control = .S q ∧ M.halt q = true

theorem rule_nonterminal {s s' : Control M} {a b : Letter M} {d : Move}
    (hr : Rule M s a s' b d) (q : M.State) (hs : s = .S q) : M.halt q = false := by
  cases hr with
  | work r ℓ hℓ => cases hs; exact r.property
  | mark => cases hs
  | scanRight => cases hs
  | record => cases hs
  | advance => cases hs
  | scanLeft => cases hs
  | finish => cases hs

theorem terminal_no_step {c c' : Config M} (ht : Terminal c) : ¬Step c c' := by
  obtain ⟨q, hsq, hhalt⟩ := ht
  rintro ⟨s, b, d, hr, _⟩
  have := rule_nonterminal hr q hsq
  simp_all

 
theorem Steps.head {n : ℕ} {c e : Config M} (h : Steps (n + 1) c e) :
    ∃ d : Config M, Step c d ∧ Steps n d e := by
  induction n generalizing c e with
  | zero =>
    cases h with
    | tail hz hs =>
      cases hz
      exact ⟨_, hs, .zero _⟩
  | succ n ih =>
    cases h with
    | tail hp hs =>
      obtain ⟨d, hfirst, hrest⟩ := ih hp
      exact ⟨d, hfirst, hrest.tail hs⟩

 

theorem Steps.terminal_length_bound {n m : ℕ} {c d e : Config M}
    (hstop : Steps n c d) (ht : Terminal d) (hother : Steps m c e) : m ≤ n := by
  induction n generalizing m c e with
  | zero =>
    cases hstop
    cases m with
    | zero => omega
    | succ m =>
      obtain ⟨e', hs, _⟩ := hother.head
      exact False.elim (terminal_no_step ht hs)
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      obtain ⟨d', hd', hrest⟩ := hstop.head
      obtain ⟨e', he', hrest'⟩ := hother.head
      have heq : d' = e' := step_deterministic hd' he'
      subst e'
      have := ih hrest hrest'
      omega

 
theorem nonhalting_arbitrarily_long (w : List M.Symbol) (r₀ : ℤ) (hr₀ : 2 ≤ r₀)
    (h : ¬M.Halts w) (n : ℕ) :
    ∃ (N : ℕ) (c : Config M), 6 * n ≤ N ∧ Steps N (initial w r₀) c := by
  have hn : ∀ j : ℕ, j < n → M.halt (M.run w j).state = false := by
    intro j _
    cases heq : M.halt (M.run w j).state with
    | false => rfl
    | true => exact False.elim (h ⟨j, heq⟩)
  obtain ⟨N, H, hN, _, hs⟩ := simulate_prefix w r₀ hr₀ n hn
  exact ⟨N, _, hN, hs⟩

 

theorem halting_iff (w : List M.Symbol) (r₀ : ℤ) (hr₀ : 2 ≤ r₀) :
    (∃ (N : ℕ) (c : Config M), Steps N (initial w r₀) c ∧ Terminal c) ↔ M.Halts w := by
  classical
  constructor
  · rintro ⟨N, c, hc, ht⟩
    by_contra hnever
    obtain ⟨K, d, hK, hs⟩ := nonhalting_arbitrarily_long w r₀ hr₀ hnever (N + 1)
    have := hc.terminal_length_bound ht hs
    omega
  · intro hhalt
    let n := Nat.find hhalt
    have hbefore : ∀ j : ℕ, j < n → M.halt (M.run w j).state = false := by
      intro j hj
      cases heq : M.halt (M.run w j).state with
      | false => rfl
      | true => exact False.elim (Nat.find_min hhalt hj heq)
    obtain ⟨N, H, _, _, hs⟩ := simulate_prefix w r₀ hr₀ n hbefore
    exact ⟨N, _, hs, (M.run w n).state, rfl, Nat.find_spec hhalt⟩

 
theorem Steps.prefix {n m : ℕ} {c d : Config M} (h : Steps n c d) (hm : m ≤ n) :
    ∃ e : Config M, Steps m c e := by
  induction h with
  | zero =>
    have he : m = 0 := by omega
    subst m
    exact ⟨_, .zero _⟩
  | @tail n c d e h hs ih =>
    by_cases he : m = n + 1
    · subst m; exact ⟨e, h.tail hs⟩
    · exact ih (by omega)

 
theorem Steps.endpoint_unique {n : ℕ} {c d e : Config M}
    (h₁ : Steps n c d) (h₂ : Steps n c e) : d = e := by
  induction h₁ generalizing e with
  | zero => cases h₂; rfl
  | tail h₁ hs ih =>
    cases h₂ with
    | tail h₂ hs₂ =>
      have he := ih h₂
      subst he
      exact step_deterministic hs hs₂

 
theorem nonhalting_every_microstep (w : List M.Symbol) (r₀ : ℤ) (hr₀ : 2 ≤ r₀)
    (h : ¬M.Halts w) (n : ℕ) : ∃! c : Config M, Steps n (initial w r₀) c := by
  obtain ⟨N, c, hN, hc⟩ := nonhalting_arbitrarily_long w r₀ hr₀ h n
  obtain ⟨d, hd⟩ := hc.prefix (show n ≤ N by omega)
  exact ⟨d, hd, fun _ he => he.endpoint_unique hd⟩

 

theorem nonhalting_execution (w : List M.Symbol) (r₀ : ℤ) (hr₀ : 2 ≤ r₀)
    (h : ¬M.Halts w) :
    ∃ c : ℕ → Config M, c 0 = initial w r₀ ∧ ∀ n : ℕ, Step (c n) (c (n + 1)) := by
  classical
  have hex : ∀ n : ℕ, ∃ c : Config M, Steps n (initial w r₀) c :=
    fun n => (nonhalting_every_microstep w r₀ hr₀ h n).exists
  choose c hc using hex
  refine ⟨c, ?_, ?_⟩
  · exact (hc 0).endpoint_unique (.zero (initial w r₀))
  · intro n
    have hn := hc (n + 1)
    cases hn with
    | tail hp hs =>
      have he := hp.endpoint_unique (hc n)
      simpa only [he] using hs
end Recorder
end Solenoidal

end OAI
