import OAI.Computability.SpaceSimulation.Machine

namespace OAI

/-! The computation to be simulated. Coordinates on each source
are relative to its head's fixed origin, on two-sided tapes. Tags
may be correlated however one likes (same tape read, etc.).
Single alphabet, with no loss of different read-only components from
a fixed common alphabet. -/
namespace Fifths

structure SingleAct (Q A : Type) (r : ℕ) where
  out : Q
  write : WriteMove A
  others : Fin r → Dir

structure Single (X : Type) where
  Q : Type
  [states : Fintype Q]
  A : Type
  [symbols : Fintype A]
  beginState : Q
  halted : Q → Bool
  heads : ℕ
  program : Q → A → (Fin heads → A) → SingleAct Q A heads
  /-- `none` tags the writable tape. -/
  sensor : List X → Option (Fin heads) → ℤ → A

attribute [instance] Single.states Single.symbols

namespace Single
variable {X : Type} (M : Single X)
instance : Nonempty M.A := ⟨M.sensor [] none 0⟩
instance : Nonempty M.Q := ⟨M.beginState⟩
abbrev Tag := Option (Fin M.heads)

structure At where
  state : M.Q
  tape : Tape M.A
  ro : Fin M.heads → ℤ

def move (q : M.Q) (s : M.A) (r : Fin M.heads → M.A) :
    SingleAct M.Q M.A M.heads :=
  if M.halted q then
    ⟨q,⟨s,.N⟩,fun _ => .N⟩
  else M.program q s r

def initial (x : List X) : M.At :=
  ⟨M.beginState,⟨0,M.sensor x none⟩, fun _ => 0⟩

def next (x : List X) (s : M.At) : M.At :=
  let t := M.move s.state s.tape.see (fun i => M.sensor x (some i) (s.ro i))
  ⟨t.out,s.tape.perform t.write,fun i => s.ro i + (t.others i).delta⟩

def atTime (M : Single X) (x : List X) : ℕ → M.At :=
  Nat.rec (M.initial x) (fun _ s => M.next x s)

abbrev Outcome := M.Q × Bool
/-- `false` flag means still running at n. -/
def finish (q : M.Q) : M.Outcome :=
  (q, M.halted q)
def outcome (x : List X) (n : ℕ) : M.Outcome :=
  M.finish (M.atTime x n).state

theorem immobile (x : List X) {s : M.At} (h : M.halted s.state = true) :
    M.next x s = s := by
  simp [next, move,h,Tape.perform,Tape.see]

theorem absorbed (x : List X) {n : ℕ} (p : (M.outcome x n).2 = true) (d : ℕ) :
    M.atTime x (n+d) = M.atTime x n := by
  change M.halted _ = true at p
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← Nat.add_assoc]
    change M.next x (M.atTime x (n+d)) = M.atTime x n
    rw [ih,M.immobile x p]

def Inside (t : ℕ) (q : ℤ) : Prop := -(t:ℤ) ≤ q ∧ q ≤ (t:ℤ)
theorem inches {t : ℕ} {q : ℤ} (h : Inside t q) (v : Dir) :
    Inside (t+1) (q+v.delta) := by
  have := v.bounds
  unfold Inside at *
  omega
theorem nearby (x : List X) (n : ℕ) :
    Inside n (M.atTime x n).tape.pos ∧ ∀ i, Inside n ((M.atTime x n).ro i) := by
  induction n with
  | zero =>
    simp [Inside,atTime,initial]
  | succ n ih =>
    rw [atTime]
    exact ⟨inches ih.1 _,fun i => inches (ih.2 i) _⟩
end Single
end Fifths

end OAI
