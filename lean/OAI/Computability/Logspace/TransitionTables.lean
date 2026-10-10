import OAI.Computability.Logspace.Deterministic

namespace OAI

/-!
Finite transition tables, configuration semantics, and reindexing into finite machines.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

/-!
A notational convenience: transition tables whose finite index sets
are not necessarily written as Fin k. Reindex back to Machine without
changing any run.
-/

namespace ExactDerandomization.Table

variable (S W H : Type)

structure Act where
  next : S
  write : W → Bool
  workMove : W → Direction
  inputMove : H → Direction

structure TM where
  start : S
  out : S → Option Bool
  go : S → (H → InputSymbol) → (W → Bool) → Bool → Act S W H

@[ext]
structure Conf (n : ℕ) where
  state : S
  inputPos : H → Fin (n + 2)
  workPos : W → ℤ
  work : W → ℤ → Bool

namespace TM

variable {S W H} (P : TM S W H)

def init (n : ℕ) : Conf S W H n :=
  ⟨P.start, fun _ => ⟨0, by omega⟩, fun _ => 0, fun _ _ => false⟩

def applyAct {n : ℕ} (c : Conf S W H n) (a : Act S W H) : Conf S W H n :=
  { state := a.next
    inputPos := fun j => (a.inputMove j).moveInput (c.inputPos j)
    workPos := fun k => (a.workMove k).move (c.workPos k)
    work := fun k => Function.update (c.work k) (c.workPos k) (a.write k) }

def step (x : Word) (coin : Bool) (c : Conf S W H x.length) : Conf S W H x.length :=
  match P.out c.state with
  | some _ => c
  | none =>
    applyAct c (P.go c.state (fun j => readInput x (c.inputPos j))
      (fun k => c.work k (c.workPos k)) coin)

def run (x : Word) (coins : CoinTape) :
    ℕ → Conf S W H x.length
  | 0 => P.init x.length
  | t+1 => P.step x (coins t) (run x coins t)

def det : Prop :=
  ∀ s i v, P.go s i v false = P.go s i v true

def spaceThrough [Fintype W] (x : Word) (coins : CoinTape) (t : ℕ) : ℕ :=
  ∑ k : W, ((Finset.range (t+1)).image (fun s => (P.run x coins s).workPos k)).card

def halts (x : Word) (t : ℕ) : Prop :=
  ∀ coins : CoinTape, ∃ b : Bool, P.out (P.run x coins t).state = some b

def prob (x : Word) (t : ℕ) : ℚ :=
  ((Finset.univ.filter (fun bits : Fin t → Bool =>
     P.out (P.run x (Machine.extendCoins bits) t).state = some true)).card : ℚ) / 2 ^ t

def idle (s : S) (v : W → Bool) : Act S W H := ⟨s, v, fun _ => .stay, fun _ => .stay⟩

theorem applyAct_idle {n : ℕ} (c : Conf S W H n) :
    applyAct c (idle c.state (fun k => c.work k (c.workPos k))) = c := by
  ext <;> simp [applyAct, idle, Direction.moveInput, Direction.move]

/-- Uniform form of step: give halting states self-loop actions writing
the scanned bits back. -/
def goStutter (s : S) (i : H → InputSymbol) (v : W → Bool) (coin : Bool) :
    Act S W H :=
  if P.out s = none then P.go s i v coin else idle s v

theorem step_eq_apply (x : Word) (coin : Bool) (c : Conf S W H x.length) :
    P.step x coin c = applyAct c (P.goStutter c.state
       (fun j => readInput x (c.inputPos j)) (fun k => c.work k (c.workPos k)) coin) := by
  cases h : P.out c.state <;> simp [step, goStutter, h, applyAct_idle]

variable {q w h : ℕ}

def reindex (e : S ≃ Fin (q+1)) (f : W ≃ Fin w) (g : H ≃ Fin h) :
    Machine q w h :=
  { initialState := e P.start
    output := fun a => P.out (e.symm a)
    transition := fun s i v coin =>
      let a := P.go (e.symm s) (fun j => i (g j)) (fun k => v (f k)) coin
      { nextState := e a.next
        write := fun k => a.write (f.symm k)
        workMove := fun k => a.workMove (f.symm k)
        inputMove := fun j => a.inputMove (g.symm j) } }

def mapConf (e : S ≃ Fin (q+1)) (f : W ≃ Fin w) (g : H ≃ Fin h)
    {n : ℕ} (c : Conf S W H n) : Configuration q w h n :=
  ⟨e c.state, fun j => c.inputPos (g.symm j), fun k => c.workPos (f.symm k),
    fun k => c.work (f.symm k)⟩

theorem step_reindex (e : S ≃ Fin (q+1)) (f : W ≃ Fin w) (g : H ≃ Fin h)
    (x : Word) (coin : Bool) (c : Conf S W H x.length) :
    (P.reindex e f g).step x coin (mapConf e f g c) =
      mapConf e f g (P.step x coin c) := by
  cases hout : P.out c.state <;>
    simp [Machine.step, reindex, mapConf, step, applyAct, hout]

theorem run_reindex (e : S ≃ Fin (q+1)) (f : W ≃ Fin w) (g : H ≃ Fin h)
    (x : Word) (coins : CoinTape) (t : ℕ) :
    (P.reindex e f g).run x coins t = mapConf e f g (P.run x coins t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Machine.run_succ, ih]
    exact P.step_reindex _ _ _ _ _ _

theorem out_reindex (e : S ≃ Fin (q+1)) (f : W ≃ Fin w) (g : H ≃ Fin h)
    (x : Word) (coins : CoinTape) (t : ℕ) :
    (P.reindex e f g).output ((P.reindex e f g).run x coins t).state =
       P.out (P.run x coins t).state := by
  rw [run_reindex]
  simp [reindex, mapConf]

theorem prob_reindex (e : S ≃ Fin (q+1)) (f : W ≃ Fin w) (g : H ≃ Fin h)
    (x : Word) (t : ℕ) :
    (P.reindex e f g).acceptanceProbability x t = P.prob x t := by
  simp only [Machine.acceptanceProbability, prob, out_reindex]

theorem space_reindex [Fintype W] (e : S ≃ Fin (q+1)) (f : W ≃ Fin w) (g : H ≃ Fin h)
    (x : Word) (coins : CoinTape) (t : ℕ) :
    (P.reindex e f g).spaceThrough x coins t = P.spaceThrough x coins t := by
  simp only [Machine.spaceThrough, spaceThrough, run_reindex, mapConf]
  exact Fintype.sum_equiv f.symm _ _ fun k => rfl

theorem det_reindex (e : S ≃ Fin (q+1)) (f : W ≃ Fin w) (g : H ≃ Fin h)
    (hp : P.det) : (P.reindex e f g).Deterministic := by
  intro s i v
  simp only [reindex, hp _ _ _]

/-- Regard a Machine as a table (no reindexing). -/
def ofMachine (M : Machine q w h) : TM (Fin (q+1)) (Fin w) (Fin h) :=
  ⟨M.initialState, M.output, fun s i v coin =>
     let a := M.transition s i v coin
     ⟨a.nextState, a.write, a.workMove, a.inputMove⟩⟩

@[simp] theorem reindex_refl (M : Machine q w h) :
    (ofMachine M).reindex (.refl _) (.refl _) (.refl _) = M := rfl

/-- The index equivalence is routine, but we record it to compile a nonempty-state
table to the concrete Machine class. -/
noncomputable def number [Fintype S] [Nonempty S] :
    S ≃ Fin (Fintype.card S - 1 + 1) :=
  (Fintype.equivFin S).trans (finCongr (by have := Fintype.card_pos (α:=S); omega))

end TM
end ExactDerandomization.Table

end

end OAI
