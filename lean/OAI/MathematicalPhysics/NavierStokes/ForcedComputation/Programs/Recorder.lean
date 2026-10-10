import Mathlib

namespace OAI

/-!
The seven-row reversible recording table in Section 2 of *Finite Instructions
and Solenoidal Shear Flows* (2026), Lemma `lem:recorder`.

The inverse below is valid on the entire guarded domain, including tapes that
do not satisfy the checkpoint invariant.  The record is the pair consisting of
the original state and the symbol read, as in Bennett, *Logical reversibility
of computation* (1973), equations (9)--(11); the concrete seven-row construction
and its proof are supplied here rather than assumed from that reference.
-/

namespace ForcedComputation.Recorder

variable {Q A : Type*}

structure Machine (Q A : Type*) where
  halting : Q → Bool
  next : Q → A → Q
  write : Q → A → A
  move : Q → A → ℤ
  move_bound : ∀ q a, -1 ≤ move q a ∧ move q a ≤ 1

abbrev Record (Q A : Type*) := Q × A

inductive History (Q A : Type*)
  | empty
  | frontier
  | record (r : Record Q A)
  deriving DecidableEq, Fintype

inductive Control (Q A : Type*)
  | checkpoint (q : Q)
  | mark (r : Record Q A)
  | scanRight (r : Record Q A)
  | advance (q : Q)
  | scanLeft (q : Q)
  deriving DecidableEq, Fintype

abbrev Symbol (Q A : Type*) := A × History Q A × Bool

open History Control

/-- Exactly the seven rows of the manuscript's guarded local table. -/
inductive LocalStep (M : Machine Q A) :
    Control Q A → Symbol Q A → Control Q A → Symbol Q A → ℤ → Prop
  | work (q : Q) (a : A) (l : History Q A)
      (hq : M.halting q = false) (hl : l ≠ frontier) :
      LocalStep M (checkpoint q) (a, l, false)
        (mark (q, a)) (M.write q a, l, false) (M.move q a)
  | setMark (r : Record Q A) (c : A) (l : History Q A) (hl : l ≠ frontier) :
      LocalStep M (mark r) (c, l, false) (scanRight r) (c, l, true) 1
  | right (r : Record Q A) (c : A) (l : History Q A) (hl : l ≠ frontier) :
      LocalStep M (scanRight r) (c, l, false) (scanRight r) (c, l, false) 1
  | record (r : Record Q A) (c : A) :
      LocalStep M (scanRight r) (c, frontier, false)
        (advance (M.next r.1 r.2)) (c, History.record r, false) 1
  | advance (q : Q) (c : A) :
      LocalStep M (Control.advance q) (c, empty, false)
        (scanLeft q) (c, frontier, false) (-1)
  | left (q : Q) (c : A) (l : History Q A) (hl : l ≠ frontier) :
      LocalStep M (scanLeft q) (c, l, false) (scanLeft q) (c, l, false) (-1)
  | clearMark (q : Q) (c : A) (l : History Q A) (hl : l ≠ frontier) :
      LocalStep M (scanLeft q) (c, l, true) (checkpoint q) (c, l, false) 0

def incoming (M : Machine Q A) : Control Q A → ℤ
  | checkpoint _ => 0
  | mark r => M.move r.1 r.2
  | scanRight _ => 1
  | advance _ => 1
  | scanLeft _ => -1

theorem LocalStep.incoming_eq {M : Machine Q A} {q q' : Control Q A}
    {s s' : Symbol Q A} {d : ℤ} (h : LocalStep M q s q' s' d) :
    incoming M q' = d := by
  cases h <;> rfl

/-- Reconstruct the preceding control and read symbol from the new control and
the complete symbol that was written. No checkpoint invariant is consulted. -/
def undoLocal : Control Q A → Symbol Q A → Option (Control Q A × Symbol Q A)
  | checkpoint q, (c, l, _) => some (scanLeft q, (c, l, true))
  | mark r, (_, l, _) => some (checkpoint r.1, (r.2, l, false))
  | scanRight r, (c, l, true) => some (mark r, (c, l, false))
  | scanRight r, (c, l, false) => some (scanRight r, (c, l, false))
  | advance _, (c, History.record r, _) => some (scanRight r, (c, frontier, false))
  | advance _, _ => none
  | scanLeft q, (c, History.frontier, _) => some (advance q, (c, empty, false))
  | scanLeft q, (c, l, _) => some (scanLeft q, (c, l, false))

theorem LocalStep.undo {M : Machine Q A} {q q' : Control Q A}
    {s s' : Symbol Q A} {d : ℤ} (h : LocalStep M q s q' s' d) :
    undoLocal q' s' = some (q, s) := by
  cases h with
  | work => rfl
  | setMark => rfl
  | right => rfl
  | record => rfl
  | advance => rfl
  | left q c l hl => cases l <;> simp_all [undoLocal]
  | clearMark => rfl

theorem LocalStep.predecessor_unique {M : Machine Q A}
    {q₁ q₂ q' : Control Q A} {s₁ s₂ s' : Symbol Q A} {d₁ d₂ : ℤ}
    (h₁ : LocalStep M q₁ s₁ q' s' d₁) (h₂ : LocalStep M q₂ s₂ q' s' d₂) :
    q₁ = q₂ ∧ s₁ = s₂ ∧ d₁ = d₂ := by
  have h := Option.some.inj (h₁.undo.symm.trans h₂.undo)
  exact ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2,
    h₁.incoming_eq.symm.trans h₂.incoming_eq⟩

/-- A terminating local interpreter for the finite table. -/
def evalLocal [DecidableEq Q] [DecidableEq A] (M : Machine Q A)
    (q : Control Q A) (s : Symbol Q A) : Option (Control Q A × Symbol Q A × ℤ) :=
  match q, s with
  | checkpoint q, (a, l, false) =>
    if M.halting q = false ∧ l ≠ frontier then
      some (mark (q, a), (M.write q a, l, false), M.move q a) else none
  | mark r, (c, l, false) =>
    if l ≠ frontier then some (scanRight r, (c, l, true), 1) else none
  | scanRight r, (c, l, false) =>
    if l = frontier then some (advance (M.next r.1 r.2), (c, History.record r, false), 1)
    else some (scanRight r, (c, l, false), 1)
  | advance q, (c, empty, false) => some (scanLeft q, (c, frontier, false), -1)
  | scanLeft q, (c, l, b) =>
    if l ≠ frontier then
      if b then some (checkpoint q, (c, l, false), 0)
      else some (scanLeft q, (c, l, false), -1)
    else none
  | _, _ => none

theorem LocalStep.eval [DecidableEq Q] [DecidableEq A] {M : Machine Q A}
    {q q' : Control Q A} {s s' : Symbol Q A} {d : ℤ}
    (h : LocalStep M q s q' s' d) : evalLocal M q s = some (q', s', d) := by
  cases h <;> simp_all [evalLocal]

theorem LocalStep.successor_unique [DecidableEq Q] [DecidableEq A]
    {M : Machine Q A} {q q₁ q₂ : Control Q A} {s s₁ s₂ : Symbol Q A} {d₁ d₂ : ℤ}
    (h₁ : LocalStep M q s q₁ s₁ d₁) (h₂ : LocalStep M q s q₂ s₂ d₂) :
    q₁ = q₂ ∧ s₁ = s₂ ∧ d₁ = d₂ := by
  have h := Prod.mk.inj (Option.some.inj (h₁.eval.symm.trans h₂.eval))
  exact ⟨h.1, (Prod.mk.inj h.2).1, (Prod.mk.inj h.2).2⟩

structure Configuration (Q A : Type*) where
  control : Control Q A
  head : ℤ
  tape : ℤ → Symbol Q A

def Step (M : Machine Q A) (C D : Configuration Q A) : Prop :=
  ∃ q' s' d, LocalStep M C.control (C.tape C.head) q' s' d ∧
    D = ⟨q', C.head + d, Function.update C.tape C.head s'⟩

def undo (M : Machine Q A) (D : Configuration Q A) : Option (Configuration Q A) :=
  let h := D.head - incoming M D.control
  (undoLocal D.control (D.tape h)).map fun p =>
    ⟨p.1, h, Function.update D.tape h p.2⟩

/-- The entire predecessor tape, head, and control are recovered. -/
theorem Step.undo {M : Machine Q A} {C D : Configuration Q A} (h : Step M C D) :
    undo M D = some C := by
  obtain ⟨q', s', d, hlocal, rfl⟩ := h
  have hhead : C.head + d - incoming M q' = C.head := by
    rw [hlocal.incoming_eq]
    omega
  change (undoLocal q' ((Function.update C.tape C.head s')
    (C.head + d - incoming M q'))).map (fun p =>
      ⟨p.1, C.head + d - incoming M q',
        Function.update (Function.update C.tape C.head s')
          (C.head + d - incoming M q') p.2⟩) = some C
  rw [hhead, Function.update_self, hlocal.undo, Option.map_some]
  congr 1
  have ht : Function.update (Function.update C.tape C.head s') C.head (C.tape C.head) =
      C.tape := by
    funext j
    by_cases hj : j = C.head <;> simp [hj]
  rw [ht]

theorem Step.predecessor_unique {M : Machine Q A} {C₁ C₂ D : Configuration Q A}
    (h₁ : Step M C₁ D) (h₂ : Step M C₂ D) : C₁ = C₂ :=
  Option.some.inj (h₁.undo.symm.trans h₂.undo)

theorem Step.scan_right {M : Machine Q A} {r : Record Q A} {h : ℤ}
    {tape : ℤ → Symbol Q A} {c : A} {l : History Q A}
    (hs : tape h = (c, l, false)) (hl : l ≠ frontier) :
    Step M ⟨scanRight r, h, tape⟩ ⟨scanRight r, h + 1, tape⟩ := by
  refine ⟨scanRight r, (c, l, false), 1, ?_, ?_⟩
  · simpa only [hs] using LocalStep.right (M := M) r c l hl
  · simp only
    rw [← hs, Function.update_eq_self]

theorem Step.scan_left {M : Machine Q A} {q : Q} {h : ℤ}
    {tape : ℤ → Symbol Q A} {c : A} {l : History Q A}
    (hs : tape h = (c, l, false)) (hl : l ≠ frontier) :
    Step M ⟨scanLeft q, h, tape⟩ ⟨scanLeft q, h - 1, tape⟩ := by
  refine ⟨scanLeft q, (c, l, false), -1, ?_, ?_⟩
  · simpa only [hs] using LocalStep.left (M := M) q c l hl
  · simp only
    rw [← hs, Function.update_eq_self]
    congr 1

/-- Execution with an exact finite number of local transitions. -/
inductive Steps (M : Machine Q A) : ℕ → Configuration Q A → Configuration Q A → Prop
  | zero (C) : Steps M 0 C C
  | next {n C D E} : Steps M n C D → Step M D E → Steps M (n + 1) C E

theorem Steps.trans {M : Machine Q A} {m n : ℕ} {C D E : Configuration Q A}
    (h₁ : Steps M m C D) (h₂ : Steps M n D E) : Steps M (m + n) C E := by
  induction h₂ with
  | zero => simpa using h₁
  | next h₂ hstep ih => simpa [Nat.add_assoc] using Steps.next (ih h₁) hstep

theorem scan_right_steps (M : Machine Q A) (r : Record Q A)
    (h : ℤ) (tape : ℤ → Symbol Q A) (n : ℕ)
    (hs : ∀ i < n, ∃ c l, tape (h + (i : ℤ)) = (c, l, false) ∧ l ≠ frontier) :
    Steps M n ⟨scanRight r, h, tape⟩ ⟨scanRight r, h + (n : ℤ), tape⟩ := by
  induction n with
  | zero => simpa using Steps.zero (M := M) ⟨scanRight r, h, tape⟩
  | succ n ih =>
    obtain ⟨c, l, he, hl⟩ := hs n (Nat.lt_succ_self n)
    have hn := ih (fun i hi => hs i (Nat.lt_succ_of_lt hi))
    have hstep := Step.scan_right (M := M) (r := r) he hl
    convert Steps.next hn hstep using 1
    simp [Nat.cast_add, Nat.cast_one, add_assoc]

theorem scan_left_steps (M : Machine Q A) (q : Q)
    (h : ℤ) (tape : ℤ → Symbol Q A) (n : ℕ)
    (hs : ∀ i < n, ∃ c l, tape (h - (i : ℤ)) = (c, l, false) ∧ l ≠ frontier) :
    Steps M n ⟨scanLeft q, h, tape⟩ ⟨scanLeft q, h - (n : ℤ), tape⟩ := by
  induction n with
  | zero => simpa using Steps.zero (M := M) ⟨scanLeft q, h, tape⟩
  | succ n ih =>
    obtain ⟨c, l, he, hl⟩ := hs n (Nat.lt_succ_self n)
    have hn := ih (fun i hi => hs i (Nat.lt_succ_of_lt hi))
    have hstep := Step.scan_left (M := M) (q := q) he hl
    convert Steps.next hn hstep using 1
    simp [Nat.cast_add, Nat.cast_one, sub_sub]

def tracks (w : ℤ → A) (h : ℤ → History Q A) (b : ℤ → Bool) : ℤ → Symbol Q A :=
  fun j => (w j, h j, b j)

theorem tracks_update_work (w : ℤ → A) (h : ℤ → History Q A) (b : ℤ → Bool)
    (j : ℤ) (a : A) :
    Function.update (tracks w h b) j (a, h j, b j) =
      tracks (Function.update w j a) h b := by
  funext k
  by_cases hk : k = j <;> simp [tracks, hk]

theorem tracks_update_history (w : ℤ → A) (h : ℤ → History Q A) (b : ℤ → Bool)
    (j : ℤ) (l : History Q A) :
    Function.update (tracks w h b) j (w j, l, b j) =
      tracks w (Function.update h j l) b := by
  funext k
  by_cases hk : k = j <;> simp [tracks, hk]

theorem tracks_update_mark (w : ℤ → A) (h : ℤ → History Q A) (b : ℤ → Bool)
    (j : ℤ) (v : Bool) :
    Function.update (tracks w h b) j (w j, h j, v) =
      tracks w h (Function.update b j v) := by
  funext k
  by_cases hk : k = j <;> simp [tracks, hk]

/-- A complete recorder cycle.  There are `k` right-scan steps and `k + 1`
left-scan steps, in addition to the five non-scan transitions.  The hypotheses
describe the actual work/history tracks, not a pre-assumed simulation. -/
theorem checkpoint_cycle (M : Machine Q A) (q : Q) (w : ℤ → A)
    (history : ℤ → History Q A) (head : ℤ) (k : ℕ)
    (hq : M.halting q = false)
    (hhead : history head ≠ frontier)
    (hbefore : ∀ j < head + M.move q (w head) + (k : ℤ) + 1,
      history j ≠ frontier)
    (hfront : history (head + M.move q (w head) + (k : ℤ) + 1) = frontier)
    (hempty : history (head + M.move q (w head) + (k : ℤ) + 1 + 1) = empty) :
    let r : Record Q A := (q, w head)
    let head' := head + M.move q (w head)
    let g := head' + (k : ℤ) + 1
    let w' := Function.update w head (M.write q (w head))
    let history' := Function.update (Function.update history g (History.record r))
      (g + 1) frontier
    Steps M (2 * k + 6)
      ⟨checkpoint q, head, tracks w history (fun _ => false)⟩
      ⟨checkpoint (M.next q (w head)), head', tracks w' history' (fun _ => false)⟩ := by
  dsimp only
  let r : Record Q A := (q, w head)
  let head' := head + M.move q (w head)
  let g := head' + (k : ℤ) + 1
  let w' := Function.update w head (M.write q (w head))
  let marks : ℤ → Bool := Function.update (fun _ => false) head' true
  let hist₁ := Function.update history g (History.record r)
  let hist₂ := Function.update hist₁ (g + 1) frontier
  have hh'g : head' < g := by dsimp [g]; omega
  have hhfront : history head' ≠ frontier := hbefore head' hh'g
  have hg : history g = frontier := hfront
  have hge : history (g + 1) = empty := hempty
  have hm (j : ℤ) (hj : j ≠ head') : marks j = false := by
    simp [marks, Function.update_of_ne hj]
  have hmark : marks head' = true := by simp [marks]
  have h₁ : Step M
      ⟨checkpoint q, head, tracks w history (fun _ => false)⟩
      ⟨mark r, head', tracks w' history (fun _ => false)⟩ := by
    refine ⟨mark r, (M.write q (w head), history head, false), M.move q (w head),
      LocalStep.work q (w head) (history head) hq hhead, ?_⟩
    simp only [tracks_update_work]
    rfl
  have h₂ : Step M
      ⟨mark r, head', tracks w' history (fun _ => false)⟩
      ⟨scanRight r, head' + 1, tracks w' history marks⟩ := by
    refine ⟨scanRight r, (w' head', history head', true), 1,
      LocalStep.setMark r (w' head') (history head') hhfront, ?_⟩
    simp only [tracks_update_mark]
    rfl
  have hR : Steps M k
      ⟨scanRight r, head' + 1, tracks w' history marks⟩
      ⟨scanRight r, g, tracks w' history marks⟩ := by
    have hs : ∀ i < k, ∃ c l,
        tracks w' history marks (head' + 1 + (i : ℤ)) = (c, l, false) ∧
          l ≠ frontier := by
      intro i hi
      refine ⟨w' (head' + 1 + (i : ℤ)), history (head' + 1 + (i : ℤ)), ?_,
        hbefore (head' + 1 + (i : ℤ)) ?_⟩
      · dsimp only [tracks]
        rw [hm _ (by omega)]
      · dsimp [g, head'] at *
        omega
    convert scan_right_steps M r (head' + 1) (tracks w' history marks) k hs using 1
    congr 1
    dsimp [g]
    omega
  have h₃ : Step M
      ⟨scanRight r, g, tracks w' history marks⟩
      ⟨advance (M.next q (w head)), g + 1, tracks w' hist₁ marks⟩ := by
    refine ⟨advance (M.next q (w head)), (w' g, History.record r, false), 1, ?_, ?_⟩
    · simpa only [tracks, hg, hm g (by omega)] using LocalStep.record (M := M) r (w' g)
    · rw [← hm g (by omega), tracks_update_history]
  have h₄ : Step M
      ⟨advance (M.next q (w head)), g + 1, tracks w' hist₁ marks⟩
      ⟨scanLeft (M.next q (w head)), g, tracks w' hist₂ marks⟩ := by
    have he : hist₁ (g + 1) = empty := by
      simpa [hist₁, Function.update_of_ne (show g + 1 ≠ g by omega)] using hge
    refine ⟨scanLeft (M.next q (w head)), (w' (g + 1), frontier, false), -1, ?_, ?_⟩
    · simpa only [tracks, he, hm (g + 1) (by omega)] using
        LocalStep.advance (M := M) (M.next q (w head)) (w' (g + 1))
    · rw [← hm (g + 1) (by omega), tracks_update_history]
      change (⟨scanLeft (M.next q (w head)), g, tracks w' hist₂ marks⟩ :
        Configuration Q A) = ⟨scanLeft (M.next q (w head)), (g + 1) + (-1),
          tracks w' hist₂ marks⟩
      congr 1
      omega
  have hL : Steps M (k + 1)
      ⟨scanLeft (M.next q (w head)), g, tracks w' hist₂ marks⟩
      ⟨scanLeft (M.next q (w head)), head', tracks w' hist₂ marks⟩ := by
    have hs : ∀ i < k + 1, ∃ c l,
        tracks w' hist₂ marks (g - (i : ℤ)) = (c, l, false) ∧ l ≠ History.frontier := by
      intro i hi
      have hji : head' < g - (i : ℤ) := by dsimp [g]; omega
      have hjg : g - (i : ℤ) ≤ g := by omega
      refine ⟨w' (g - (i : ℤ)), hist₂ (g - (i : ℤ)), ?_, ?_⟩
      · dsimp only [tracks]
        rw [hm _ (by omega)]
      · dsimp only [hist₂]
        rw [Function.update_of_ne (by omega)]
        by_cases hgg : g - (i : ℤ) = g
        · simp [hist₁, hgg]
        · rw [show hist₁ (g - (i : ℤ)) = history (g - (i : ℤ)) by
            exact Function.update_of_ne hgg _ _]
          exact hbefore _ (lt_of_le_of_ne hjg hgg)
    convert scan_left_steps M (M.next q (w head)) g (tracks w' hist₂ marks) (k + 1) hs using 1
    congr 1
    dsimp [g]
    omega
  have h₅ : Step M
      ⟨scanLeft (M.next q (w head)), head', tracks w' hist₂ marks⟩
      ⟨checkpoint (M.next q (w head)), head', tracks w' hist₂ (fun _ => false)⟩ := by
    have hh : hist₂ head' = history head' := by
      simp [hist₂, hist₁, Function.update_of_ne (show head' ≠ g + 1 by omega),
        Function.update_of_ne (show head' ≠ g by omega)]
    refine ⟨checkpoint (M.next q (w head)), (w' head', hist₂ head', false), 0, ?_, ?_⟩
    · simpa only [tracks, hmark] using
        LocalStep.clearMark (M := M) (M.next q (w head)) (w' head') (hist₂ head')
          (by simpa only [hh] using hhfront)
    · rw [tracks_update_mark]
      have hmclear : Function.update marks head' false = fun _ => false := by
        funext j
        by_cases hj : j = head' <;> simp [marks, hj]
      rw [hmclear]
      simp
  have h12 := Steps.next (Steps.next (Steps.zero _) h₁) h₂
  have h123 := Steps.next (h12.trans hR) h₃
  have h1234 := Steps.next h123 h₄
  have result := Steps.next (h1234.trans hL) h₅
  convert result using 1
  omega

end ForcedComputation.Recorder

end OAI
