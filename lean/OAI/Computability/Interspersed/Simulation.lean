import Mathlib
import OAI.Computability.Interspersed.Erasure

namespace OAI

/-! Initialized interspersed executions and ordinary work-tape halting. -/

noncomputable section
open scoped ContDiff
namespace PrefixFlows
namespace Interspersed
variable {Q A : Type*} {H : Set Q}
abbrev WorkConfig (Q A : Type*) := Q × Stack A × Stack A

 

def workNext (δ : Q → A → Q × A × Move) (s : WorkConfig Q A) : WorkConfig Q A :=
  let (q', b, d) := δ s.1 (s.2.2 0)
  match d with
  | .stay => (q', s.2.1, push b (tail s.2.2))
  | .right => (q', push b s.2.1, tail s.2.2)
  | .left => (q', tail s.2.1, push (s.2.1 0) (push b (tail s.2.2)))

 

def Represents (blank : A) (c : Config Q A H) (s : WorkConfig Q A) : Prop :=
  (∃ h, c.1 = .main s.1 h) ∧ Erases blank c.2.1 s.2.1 ∧
    Erases blank c.2.2 s.2.2 ∧ ∃ a, c.2.2 0 = .inl a

 

theorem simulate_work_step (δ : Q → A → Q × A × Move) (blank : A)
    {c : Config Q A H} {s : WorkConfig Q A} (hc : Represents blank c s)
    (hs : s.1 ∉ H) :
    ∃ k d, 0 < k ∧ Exec δ k c d ∧ Represents blank d (workNext δ s) := by
  rcases c with ⟨ctrl, L, Rfull⟩
  rcases s with ⟨q, LW, RWfull⟩
  rcases hc with ⟨⟨h, rfl⟩, hL, hR, ⟨a, ha⟩⟩
  change q ∉ H at hs
  change Erases blank L LW at hL
  change Erases blank Rfull RWfull at hR
  change Rfull 0 = Sum.inl a at ha
  obtain ⟨R, rfl⟩ : ∃ R, Rfull = push (.inl a) R := by
    refine ⟨(fun k => Rfull (k + 1)), ?_⟩
    have he := (stack_eta Rfull).symm
    rw [ha] at he
    exact he
  rcases hR.work_inv with ⟨RW, hRW, hRt⟩
  subst RWfull
  let qn : {q : Q // q ∉ H} := ⟨q, hs⟩
  rcases hd : δ q a with ⟨q', b, d⟩
  cases d with
  | stay =>
    refine ⟨1, (.main q' .stay, push (.inr (qn, h, a)) L, push (.inl b) R),
      by omega, main_stay δ qn h a b q' hd L R, ?_⟩
    simp only [workNext, push_zero, hd, tail_push]
    exact ⟨⟨.stay, rfl⟩, .record _ hL, .work _ hRt, b, rfl⟩
  | right =>
    rcases hRt.eventually_blank with ⟨n, hn⟩
    rcases split_at_work blank hn with ⟨gs, a', R', hgs, rfl⟩
    rcases (Erases.of_prepend_records gs hRt).work_inv with ⟨RW', rfl, hR'⟩
    refine ⟨gs.length + 2,
      (.main q' .right,
        prepend (gs.reverse.map Sum.inr) (push (.inl b) (push (.inr (qn, h, a)) L)),
        push (.inl a') R'), by omega, main_right δ qn h a b a' q' hd gs L R', ?_⟩
    simp only [workNext, push_zero, hd, tail_push]
    exact ⟨⟨.right, rfl⟩, Erases.prepend_records gs.reverse (Erases.work b (Erases.record _ hL)),
      .work a' hR', a', rfl⟩
  | left =>
    rcases hL.eventually_blank with ⟨n, hn⟩
    rcases split_at_work blank hn with ⟨gs, a', L', hgs, rfl⟩
    rcases (hL.of_prepend_records gs).work_inv with ⟨LW', rfl, hL'⟩
    refine ⟨gs.length + 2,
      (.main q' .left, L',
        push (.inl a') (prepend (gs.reverse.map Sum.inr)
          (push (.inl b) (push (.inr (qn, h, a)) R)))), by omega,
      main_left δ qn h a b a' q' hd gs L' R, ?_⟩
    simp only [workNext, push_zero, hd, tail_push]
    exact ⟨⟨.left, rfl⟩, hL',
      .work a' (Erases.prepend_records gs.reverse (Erases.work b (Erases.record _ hRt))), a', rfl⟩

 
theorem Exec.append {δ : Q → A → Q × A × Move} {n m : ℕ}
    {c d e : Config Q A H} (h : Exec δ n c d) (h' : Exec δ m d e) :
    Exec δ (n + m) c e := by
  induction h with
  | zero c => simpa using h'
  | succ hs he ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Exec.succ hs (ih h')

 

theorem Exec.length_le_of_terminal {δ : Q → A → Q × A × Move} {n : ℕ}
    {c d : Config Q A H} (h : Exec δ n c d) (hd : ¬ ∃ e, Step δ d e) :
    ∀ {m : ℕ} {e : Config Q A H}, Exec δ m c e → m ≤ n := by
  induction h with
  | zero c =>
    intro m e hm
    cases hm with
    | zero => exact le_rfl
    | succ hs he => exact (hd ⟨_, hs⟩).elim
  | succ hs he ih =>
    intro m e hm
    cases hm with
    | zero => exact Nat.zero_le _
    | succ hs' he' =>
      have hd' := hs.deterministic hs'
      subst hd'
      exact Nat.succ_le_succ (ih hd he')

 

def workRun (δ : Q → A → Q × A × Move) (s : WorkConfig Q A) : ℕ → WorkConfig Q A
  | 0 => s
  | n + 1 => workNext δ (workRun δ s n)

 

theorem simulate_work_prefix (δ : Q → A → Q × A × Move) (blank : A)
    {c : Config Q A H} {s : WorkConfig Q A} (hc : Represents blank c s) :
    ∀ n, (∀ j, j < n → (workRun δ s j).1 ∉ H) →
      ∃ k d, n ≤ k ∧ Exec δ k c d ∧ Represents blank d (workRun δ s n) := by
  intro n
  induction n with
  | zero =>
    intro hn
    exact ⟨0, c, le_rfl, .zero _, hc⟩
  | succ n ih =>
    intro hn
    rcases ih (fun j hj => hn j (by omega)) with ⟨k, d, hk, hcd, hd⟩
    rcases simulate_work_step δ blank hd (hn n (by omega)) with ⟨r, e, hr, hde, he⟩
    exact ⟨k + r, e, by omega, hcd.append hde, he⟩

 

def IsHalt (c : Config Q A H) : Prop :=
  ∃ q h, q ∈ H ∧ c.1 = .main q h

theorem IsHalt.terminal (δ : Q → A → Q × A × Move)
    {c : Config Q A H} (hc : IsHalt c) : ¬ ∃ d, Step δ c d := by
  rcases c with ⟨ctrl, L, R⟩
  rcases hc with ⟨q, h, hq, he⟩
  change ctrl = .main q h at he
  subst ctrl
  exact no_step_from_halt δ q hq h L R

theorem Represents.halt_iff {blank : A} {c : Config Q A H} {s : WorkConfig Q A}
    (hc : Represents blank c s) : IsHalt c ↔ s.1 ∈ H := by
  rcases hc.1 with ⟨h, he⟩
  constructor
  · rintro ⟨q, m, hq, hctrl⟩
    have hqs : s.1 = q := (Control.main.inj (he.symm.trans hctrl)).1
    exact hqs.symm ▸ hq
  · intro hs
    exact ⟨s.1, h, hs, he⟩

 

theorem represented_halting_iff (δ : Q → A → Q × A × Move) (blank : A)
    {c : Config Q A H} {s : WorkConfig Q A} (hc : Represents blank c s) :
    (∃ k d, Exec δ k c d ∧ IsHalt d) ↔ ∃ n, (workRun δ s n).1 ∈ H := by
  classical
  constructor
  · rintro ⟨k, d, hcd, hd⟩
    by_contra hn
    have hnh (j : ℕ) : (workRun δ s j).1 ∉ H := fun hj => hn ⟨j, hj⟩
    rcases simulate_work_prefix δ blank hc (k + 1) (fun j _ => hnh j)
      with ⟨r, e, hkr, hce, he⟩
    have hrk := hcd.length_le_of_terminal (hd.terminal δ) hce
    omega
  · intro hn
    rcases simulate_work_prefix δ blank hc (Nat.find hn)
      (fun j hj => Nat.find_min hn hj) with ⟨k, d, hk, hcd, hd⟩
    exact ⟨k, d, hcd, hd.halt_iff.mpr (Nat.find_spec hn)⟩

 

def initialized (blank : A) (q : Q) (w : List A) : Config Q A H :=
  (.main q .stay, (fun _ => .inl blank), prepend (w.map Sum.inl) (fun _ => .inl blank))

def workInitialized (blank : A) (q : Q) (w : List A) : WorkConfig Q A :=
  (q, (fun _ => blank), prepend w (fun _ => blank))

theorem initialized_represents (blank : A) (q : Q) (w : List A) :
    Represents blank (initialized (H := H) blank q w) (workInitialized blank q w) := by
  refine ⟨⟨.stay, rfl⟩, .blank, Erases.prepend_work w .blank, ?_⟩
  cases w with
  | nil => exact ⟨blank, rfl⟩
  | cons a w => exact ⟨a, rfl⟩

theorem initialized_halting_iff (δ : Q → A → Q × A × Move)
    (blank : A) (q : Q) (w : List A) :
    (∃ k d, Exec δ k (initialized (H := H) blank q w) d ∧ IsHalt d) ↔
      ∃ n, (workRun δ (workInitialized blank q w) n).1 ∈ H :=
  represented_halting_iff δ blank (initialized_represents blank q w)
end Interspersed
end PrefixFlows
end

end OAI
