import Mathlib
import OAI.Computability.MaxCut.Arithmetic.GridWeight

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode.Game
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.Unweighted
variable {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E] {q N : ℕ}

abbrev Sample (Y E : Type) (q : ℕ) := Y × (E × (E × (Cube (Fin q) × Cube (Fin q))))

/-- One input-size polynomial denominator, rather than a product of all
vertex degrees. Both grid and unweighting error are uniform over all cuts. -/
def gridSize (Y E : Type) [Fintype Y] [Fintype E] (q K : ℕ) :=
  (K+1) * (Fintype.card (Sample Y E q)+1)

 theorem gridSize_pos (K : ℕ) : 0 < gridSize Y E q K := by
  unfold gridSize; positivity

noncomputable def gridWeights (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (anchor : Fin N) (K : ℕ) : Fin N → Fin N → ℚ :=
  roundedWeights (G.sampleLaw t ht) (fun a => (enum (G.queries a).1, enum (G.queries a).2))
    anchor (gridSize Y E q K) (gridSize_pos K)

 theorem gridWeights_error (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (anchor : Fin N) (K : ℕ) :
    weightedMax (fun u v => (G.gridWeights t ht enum anchor K u v : ℝ)) ≤
      weightedMax (fun u v => (G.weights t ht enum u v : ℝ)) ∧
    weightedMax (fun u v => (G.weights t ht enum u v : ℝ)) -
      weightedMax (fun u v => (G.gridWeights t ht enum anchor K u v : ℝ)) ≤ 1/(K+1 : ℝ) := by
  have h := roundedWeights_max_error (G.sampleLaw t ht)
    (fun a => (enum (G.queries a).1, enum (G.queries a).2)) anchor
    (gridSize Y E q K) (gridSize_pos K)
  have hb : (Fintype.card (Sample Y E q) : ℝ) / gridSize Y E q K ≤ 1/(K+1 : ℝ) := by
    have hK : (0 : ℝ) < K+1 := by positivity
    have hC : (0 : ℝ) < Fintype.card (Sample Y E q)+1 := by positivity
    rw [gridSize, Nat.cast_mul, Nat.cast_add, Nat.cast_add, Nat.cast_one]
    apply (div_le_div_iff₀ (mul_pos hK hC) hK).mpr
    nlinarith
  exact ⟨h.1, h.2.trans hb⟩

noncomputable def gridOutput (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (anchor : Fin N) (K : ℕ) : ScaledGraph :=
  deterministicOutput (K+1) (G.gridWeights t ht enum anchor K) (aggregate_symm _)

 theorem gridOutput_error (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (anchor : Fin N) (K : ℕ) :
    |((G.gridOutput t ht enum anchor K).graph.maxCut : ℝ) / (G.gridOutput t ht enum anchor K).scale -
      weightedMax (fun u v => (G.gridWeights t ht enum anchor K u v : ℝ))| ≤ 2/(K+1 : ℝ) := by
  simpa only [gridOutput, gridWeights, roundedWeights, Nat.cast_add, Nat.cast_one] using
    deterministicOutput_error (K+1) (by omega) _ (aggregate_symm _)
      (fun u v _ => aggregate_nonneg _ u v) (aggregate_total _)

 theorem gridOutput_complete (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (anchor : Fin N) (K : ℕ)
    (lx : X → Fin q) (ly : Y → Fin q) :
    (1+(t:ℝ))/2 - 2*(1-G.satisfied lx ly) - 3/(K+1 : ℝ) ≤
      ((G.gridOutput t ht enum anchor K).graph.maxCut : ℝ) / (G.gridOutput t ht enum anchor K).scale := by
  have hc := G.weightedMax_complete t ht enum lx ly
  have he := G.gridWeights_error t ht enum anchor K
  have hg := abs_le.mp (G.gridOutput_error t ht enum anchor K)
  linarith [show (3 : ℝ)/(K+1) = 1/(K+1) + 2/(K+1) by ring]

 theorem gridOutput_vertex_bound (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (anchor : Fin N) (K : ℕ) :
    (G.gridOutput t ht enum anchor K).graph.vertices ≤
      N*(2*((K+1)*(N+1)^2+1))^6 := deterministicOutput_vertex_bound _ _ _

/-- All game-independent constants for the rounded, executable-integer target.
This is the mathematical gap; the polynomial TM printer is still separate. -/
 theorem exists_grid_gap_parameters (α : ℝ) (hα : alphaGW < α) (hα1 : α ≤ 1) :
    ∃ (t ε y n : ℚ) (δ : ℝ) (K : ℕ) (ht : t ∈ Set.Icc (-1 : ℚ) 1),
      0 < t ∧ t < 1 ∧ 0 < ε ∧ (ε:ℝ) < 1/2 ∧ 0 < δ ∧ δ < 1/2 ∧
      0 < y ∧ 0 ≤ n ∧ (n:ℝ) < α*(y:ℝ) ∧
      (∀ {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E] {q N : ℕ}
        (G : Game X Y E q) (enum : X × Cube (Fin q) ≃ Fin N) (anchor : Fin N),
        (∃ lx ly, 1-(ε:ℝ) ≤ G.satisfied lx ly) →
        (y:ℝ) ≤ ((G.gridOutput t ht enum anchor K).graph.maxCut : ℝ) /
          (G.gridOutput t ht enum anchor K).scale) ∧
      (∀ {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E] {q N : ℕ}
        (_hq : 0 < q) (G : Game X Y E q) (enum : X × Cube (Fin q) ≃ Fin N) (anchor : Fin N),
        G.Sound δ → ((G.gridOutput t ht enum anchor K).graph.maxCut : ℝ) /
          (G.gridOutput t ht enum anchor K).scale ≤ (n:ℝ)) := by
  obtain ⟨t, η, y, n, ht0, ht1, hη, hηb, hy, hypos, hn, hnlo, hgap⟩ :=
    exists_main_gap_parameters α hα hα1
  have hηr : 0 < (η:ℝ) := by exact_mod_cast hη
  have htR : 0 < (t:ℝ) := by exact_mod_cast ht0
  have htR1 : (t:ℝ) < 1 := by exact_mod_cast ht1
  have hb : 0 ≤ borellCurve t := mul_nonneg (by positivity) (Real.arcsin_nonneg.mpr htR.le)
  have hηsmall : (η:ℝ) < 1/4 := by linarith
  obtain ⟨δ,hδ,hsound⟩ := exists_weighted_soundness t ht0 ht1 (η:ℝ) hηr
  obtain ⟨K,hlarge⟩ := exists_nat_gt (3/(η:ℝ))
  have hK : (0:ℝ) < K+1 := by positivity
  have hsmall : 3/(K+1:ℝ) ≤ (η:ℝ) := by
    have hm := (div_lt_iff₀ hηr).mp hlarge
    apply (div_le_iff₀ hK).mpr; nlinarith
  have hsmaller : 2/(K+1:ℝ) ≤ (η:ℝ) := by
    exact (div_le_div_of_nonneg_right (by norm_num) hK.le).trans hsmall
  let ht : t ∈ Set.Icc (-1:ℚ) 1 := ⟨by linarith, ht1.le⟩
  refine ⟨t,η/4,y,n,min δ (1/4),K,ht,ht0,ht1,by positivity,?_,
    lt_min hδ (by norm_num),?_,hypos,hn,hgap,?_,?_⟩
  · push_cast; linarith
  · exact (min_le_right _ _).trans_lt (by norm_num)
  · intro X Y E _ _ _ q N G enum anchor hyes
    obtain ⟨lx,ly,hsat⟩ := hyes
    have hc := G.gridOutput_complete t ht enum anchor K lx ly
    have hyR : (y:ℝ) = (1+(t:ℝ))/2-2*(η:ℝ) := by exact_mod_cast hy
    push_cast at hsat; linarith
  · intro X Y E _ _ _ q N hq G enum anchor hs
    have hs' : G.Sound δ := fun lx ly => (hs lx ly).trans (min_le_left _ _)
    have h := hsound hq G enum hs'
    have he := G.gridWeights_error t ht enum anchor K
    have hg := abs_le.mp (G.gridOutput_error t ht enum anchor K)
    change (1+2/Real.pi*Real.arcsin (t:ℝ))/2+2*(η:ℝ) < (n:ℝ) at hnlo
    linarith

end OptimalMaxCut.LongCode.Game

namespace OptimalMaxCut.CounterMachine
open Turing

inductive Tape (R : Type) where
  | input | backup | output | reg (r : R)
  deriving DecidableEq, Fintype

inductive Instruction (R L : Type) where
  | inc (r : R) (next : L)
  | dec (r : R) (positive zero : L)
  | test (r : R) (zero positive : L)
  | read (one zero empty : L)
  | back (nonempty empty : L)
  | write (b : Bool) (next : L)
  | discard (next : L)
  | jump (next : L)
  | halt

structure Data (R : Type) where
  reg : R → ℕ
  input : List Bool
  backup : List Bool
  output : List Bool

structure Configuration (R L : Type) extends Data R where
  label : Option L

variable {R L : Type} [DecidableEq R]

def Instruction.execute (i : Instruction R L) (d : Data R) : Configuration R L :=
  match i with
  | .inc r next => ⟨{ d with reg := Function.update d.reg r (d.reg r + 1) }, some next⟩
  | .dec r positive zero =>
    ⟨{ d with reg := Function.update d.reg r (d.reg r - 1) },
      some (if d.reg r = 0 then zero else positive)⟩
  | .test r zero positive => ⟨d, some (if d.reg r = 0 then zero else positive)⟩
  | .read one zero empty =>
    ⟨{ d with input := d.input.tail, backup := d.input.take 1 ++ d.backup }, some (match d.input with
      | [] => empty | true :: _ => one | false :: _ => zero)⟩
  | .back nonempty empty =>
    ⟨{ d with input := d.backup.take 1 ++ d.input, backup := d.backup.tail },
      some (if d.backup = [] then empty else nonempty)⟩
  | .write b next => ⟨{ d with output := b :: d.output }, some next⟩
  | .discard next => ⟨{d with input := d.input.tail}, some next⟩
  | .jump next => ⟨d, some next⟩
  | .halt => ⟨d, none⟩

def step (p : L → Instruction R L) (c : Configuration R L) : Option (Configuration R L) :=
  c.label.map (fun l => (p l).execute c.toData)

def tapes (d : Data R) : Tape R → List Bool
  | .input => d.input
  | .backup => d.backup
  | .output => d.output
  | .reg r => List.replicate (d.reg r) true

def embed (c : Configuration R L) : TM2.Cfg (fun _ : Tape R => Bool) L (Option Bool) :=
  ⟨c.label, none, tapes c.toData⟩

def goto (l : L) : TM2.Stmt (fun _ : Tape R => Bool) L (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => l))

def Instruction.code : Instruction R L → TM2.Stmt (fun _ : Tape R => Bool) L (Option Bool)
  | .inc r next => .push (.reg r) (fun _ => true) (goto next)
  | .dec r positive zero => .pop (.reg r) (fun _ b => b)
      (.branch (fun b => b.isSome) (goto positive) (goto zero))
  | .test r zero positive => .peek (.reg r) (fun _ b => b)
      (.branch (fun b => b.isSome) (goto positive) (goto zero))
  | .read one zero empty => .pop .input (fun _ b => b)
      (.branch (fun b => b.isSome)
        (.push .backup (fun b => b.getD false)
          (.branch (fun b => b.getD false) (goto one) (goto zero))) (goto empty))
  | .back nonempty empty => .pop .backup (fun _ b => b)
      (.branch (fun b => b.isSome)
        (.push .input (fun b => b.getD false) (goto nonempty)) (goto empty))
  | .write b next => .push .output (fun _ => b) (goto next)
  | .discard next => .pop .input (fun _ _ => none) (goto next)
  | .jump next => goto next
  | .halt => .halt

 theorem tapes_inc (d : Data R) (r : R) :
    tapes { d with reg := Function.update d.reg r (d.reg r + 1) } =
      Function.update (tapes d) (.reg r) (true :: tapes d (.reg r)) := by
  funext k
  cases k with
  | input => simp [tapes]
  | output => simp [tapes]
  | backup => simp [tapes]
  | reg s => by_cases h : s = r <;> simp [tapes, h, List.replicate_succ]

 theorem tapes_dec (d : Data R) (r : R) :
    tapes { d with reg := Function.update d.reg r (d.reg r - 1) } =
      Function.update (tapes d) (.reg r) (tapes d (.reg r)).tail := by
  funext k
  cases k with
  | input => simp [tapes]
  | output => simp [tapes]
  | backup => simp [tapes]
  | reg s => by_cases h : s = r <;> simp [tapes, h]

 theorem tapes_read (d : Data R) :
    tapes { d with input := d.input.tail, backup := d.input.take 1 ++ d.backup } =
      Function.update (Function.update (tapes d) .input d.input.tail) .backup
        (d.input.take 1 ++ d.backup) := by
  funext k; cases k <;> simp [tapes]

 theorem tapes_back (d : Data R) :
    tapes { d with input := d.backup.take 1 ++ d.input, backup := d.backup.tail } =
      Function.update (Function.update (tapes d) .backup d.backup.tail) .input
        (d.backup.take 1 ++ d.input) := by
  funext k; cases k <;> simp [tapes]

 theorem tapes_write (d : Data R) (b : Bool) :
    tapes { d with output := b :: d.output } =
      Function.update (tapes d) .output (b :: d.output) := by
  funext k; cases k <;> simp [tapes]

 theorem instruction_simulation (i : Instruction R L) (d : Data R) :
    TM2.stepAux i.code none (tapes d) = embed (i.execute d) := by
  cases i with
  | inc r next => simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes_inc]
  | dec r pos zero =>
    cases h : d.reg r with
    | zero =>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h]
      simpa [h, tapes] using (tapes_dec d r).symm
    | succ n =>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed,
        tapes, h, List.replicate_succ]
      simpa [h, tapes] using (tapes_dec d r).symm
  | test r zero pos =>
    cases h : d.reg r <;>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h, List.replicate_succ]
  | read one zero empty =>
    cases h : d.input with
    | nil =>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h]
      funext k; cases k <;> simp [tapes]
    | cons b rest =>
      cases b <;>
        simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h] <;>
        simpa [h] using (tapes_read d).symm
  | back nonempty empty =>
    cases h : d.backup with
    | nil =>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h]
      funext k; cases k <;> simp [tapes]
    | cons b rest =>
      cases b <;>
        simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h] <;>
        simpa [h] using (tapes_back d).symm
  | write b next =>
    simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes_write, tapes]
  | discard next =>
    simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed]
    funext k; cases k <;> simp [tapes]
  | jump next => rfl
  | halt => rfl

 theorem step_simulation (p : L → Instruction R L) (c : Configuration R L) :
    TM2.step (fun l => (p l).code) (embed c) = (step p c).map embed := by
  cases c with
  | mk d l =>
    cases l with
    | none => rfl
    | some l => simpa [TM2.step, step, embed] using congrArg some (instruction_simulation (p l) d)

/-- No semantic atomic arithmetic operation is being charged unit time: only
unary increment/decrement, one input/output bit, and finite jumps are atomic. -/
def machine [Fintype R] [Fintype L] (p : L → Instruction R L) (main : L) : FinTM2 where
  K := Tape R
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := L
  main := main
  σ := Option Bool
  initialState := none
  m l := (p l).code

 theorem finite_tape_alphabet [Fintype R] [Fintype L]
    (p : L → Instruction R L) (main : L) (k : (machine p main).K) :
    Finite ((machine p main).Γ k) := inferInstanceAs (Finite Bool)

end OptimalMaxCut.CounterMachine

namespace OptimalMaxCut.CounterMachine
variable {R L : Type} [DecidableEq R]

/-- A structured program still has only finitely many syntactic labels.
`loop r c` tests/decrements its own unary counter, then runs `c`. It is a genuine
while loop: no claim of termination is built into the syntax. -/
inductive Command (R : Type) where
  | skip
  | inc (r : R)
  | dec (r : R)
  | write (b : Bool)
  | discard
  | rewind
  | seq (first second : Command R)
  | test (r : R) (zero positive : Command R)
  | read (one zero empty : Command R)
  | loop (r : R) (body : Command R)

namespace Command

def Label : Command R → Type
  | .skip | .inc _ | .dec _ | .write _ | .discard | .rewind => Unit
  | .seq a b => Label a ⊕ Label b
  | .test _ a b => Unit ⊕ Label a ⊕ Label b
  | .read a b c => Unit ⊕ Label a ⊕ Label b ⊕ Label c
  | .loop _ b => Unit ⊕ Label b

noncomputable instance labelFintype (c : Command R) : Fintype (Label c) := by
  induction c with
  | skip | inc | dec | write | discard | rewind => exact inferInstanceAs (Fintype Unit)
  | seq a b ia ib => exact inferInstanceAs (Fintype (Label a ⊕ Label b))
  | test r a b ia ib => exact inferInstanceAs (Fintype (Unit ⊕ Label a ⊕ Label b))
  | read a b c ia ib ic => exact inferInstanceAs (Fintype (Unit ⊕ Label a ⊕ Label b ⊕ Label c))
  | loop r b ib => exact inferInstanceAs (Fintype (Unit ⊕ Label b))

def entry : (c : Command R) → Label c
  | .skip | .inc _ | .dec _ | .write _ | .discard | .rewind => ()
  | .seq a _ => .inl a.entry
  | .test _ _ _ | .read _ _ _ | .loop _ _ => .inl ()

def code : (c : Command R) → (Label c → L) → L → Label c → Instruction R L
  | .skip, _, exit, _ => .jump exit
  | .inc r, _, exit, _ => .inc r exit
  | .dec r, _, exit, _ => .dec r exit exit
  | .write b, _, exit, _ => .write b exit
  | .discard, _, exit, _ => .discard exit
  | .rewind, labels, exit, _ => .back (labels ()) exit
  | .seq a b, labels, _exit, .inl l =>
      a.code (fun l => labels (.inl l)) (labels (.inr b.entry)) l
  | .seq _a b, labels, exit, .inr l => b.code (fun l => labels (.inr l)) exit l
  | .test r a b, labels, _, .inl _ =>
      .test r (labels (.inr (.inl a.entry))) (labels (.inr (.inr b.entry)))
  | .test _ a _, labels, exit, .inr (.inl l) =>
      a.code (fun l => labels (.inr (.inl l))) exit l
  | .test _ _ b, labels, exit, .inr (.inr l) =>
      b.code (fun l => labels (.inr (.inr l))) exit l
  | .read a b c, labels, _, .inl _ =>
      .read (labels (.inr (.inl a.entry))) (labels (.inr (.inr (.inl b.entry))))
        (labels (.inr (.inr (.inr c.entry))))
  | .read a _ _, labels, exit, .inr (.inl l) =>
      a.code (fun l => labels (.inr (.inl l))) exit l
  | .read _ b _, labels, exit, .inr (.inr (.inl l)) =>
      b.code (fun l => labels (.inr (.inr (.inl l)))) exit l
  | .read _ _ c, labels, exit, .inr (.inr (.inr l)) =>
      c.code (fun l => labels (.inr (.inr (.inr l)))) exit l
  | .loop r b, labels, exit, .inl _ => .dec r (labels (.inr b.entry)) exit
  | .loop _ b, labels, _, .inr l => b.code (fun l => labels (.inr l)) (labels (.inl ())) l

def incData (d : Data R) (r : R) : Data R :=
  { d with reg := Function.update d.reg r (d.reg r + 1) }
def decData (d : Data R) (r : R) : Data R :=
  { d with reg := Function.update d.reg r (d.reg r - 1) }
def readData (d : Data R) : Data R :=
  { d with input := d.input.tail, backup := d.input.take 1 ++ d.backup }
def backData (d : Data R) : Data R :=
  { d with input := d.backup.take 1 ++ d.input, backup := d.backup.tail }
def discardData (d : Data R) : Data R := {d with input := d.input.tail}
def writeData (d : Data R) (b : Bool) : Data R := { d with output := b :: d.output }

/-- Timed operational semantics. Loop termination and the number of iterations
must be proved by the caller; there is no hidden bounded-search oracle. -/
inductive Evaluates : Command R → Data R → Data R → ℕ → Prop
  | skip (d) : Evaluates .skip d d 1
  | inc (d r) : Evaluates (.inc r) d (incData d r) 1
  | dec (d r) : Evaluates (.dec r) d (decData d r) 1
  | write (d b) : Evaluates (.write b) d (writeData d b) 1
  | discard (d) : Evaluates .discard d (discardData d) 1
  | rewind_empty {d} : d.backup = [] → Evaluates .rewind d d 1
  | rewind_cons {d e n b rest} : d.backup = b :: rest →
      Evaluates .rewind (backData d) e n → Evaluates .rewind d e (1 + n)
  | seq {a b d e f n m} : Evaluates a d e n → Evaluates b e f m →
      Evaluates (.seq a b) d f (n + m)
  | test_zero {r a b d e n} : d.reg r = 0 → Evaluates a d e n →
      Evaluates (.test r a b) d e (1 + n)
  | test_pos {r a b d e n} : d.reg r ≠ 0 → Evaluates b d e n →
      Evaluates (.test r a b) d e (1 + n)
  | read_one {a b c d e n rest} : d.input = true :: rest →
      Evaluates a (readData d) e n → Evaluates (.read a b c) d e (1 + n)
  | read_zero {a b c d e n rest} : d.input = false :: rest →
      Evaluates b (readData d) e n → Evaluates (.read a b c) d e (1 + n)
  | read_empty {a b c d e n} : d.input = [] →
      Evaluates c (readData d) e n → Evaluates (.read a b c) d e (1 + n)
  | loop_zero {r b d} : d.reg r = 0 → Evaluates (.loop r b) d d 1
  | loop_pos {r b d e f n m} : d.reg r ≠ 0 →
      Evaluates b (decData d r) e n → Evaluates (.loop r b) e f m →
      Evaluates (.loop r b) d f (1 + n + m)

end Command

/-- Propagation through halt is explicit, as in the supplied TM2 support. -/
def advance (p : L → Instruction R L) : Option (Configuration R L) → Option (Configuration R L) :=
  fun c => c.bind (step p)

def atCfg (l : L) (d : Data R) : Option (Configuration R L) := some ⟨d, some l⟩

def Runs (p : L → Instruction R L) (n : ℕ) (l : L) (d : Data R) (l' : L) (d' : Data R) : Prop :=
  (advance p)^[n] (atCfg l d) = atCfg l' d'

 theorem runs_one (p : L → Instruction R L) (l : L) (d : Data R) (l' : L) (d' : Data R)
    (h : (p l).execute d = ⟨d', some l'⟩) : Runs p 1 l d l' d' := by
  simpa [Runs, advance, atCfg, step] using congrArg some h

 theorem Runs.trans {p : L → Instruction R L} {n m : ℕ} {l l' l'' : L} {d e f : Data R}
    (h : Runs p n l d l' e) (h' : Runs p m l' e l'' f) : Runs p (n + m) l d l'' f := by
  unfold Runs at *
  rw [Nat.add_comm n m, Function.iterate_add_apply, h, h']

namespace Command
 theorem trace {c : Command R} {d d' : Data R} {n : ℕ} (h : Evaluates c d d' n)
    (p : L → Instruction R L) (labels : c.Label → L) (exit : L)
    (atLabels : ∀ l, p (labels l) = c.code labels exit l) :
    Runs p n (labels c.entry) d exit d' := by
  induction h generalizing L with
  | skip d =>
    apply runs_one
    rw [atLabels]; rfl
  | inc d r =>
    apply runs_one
    rw [atLabels]; rfl
  | dec d r =>
    apply runs_one
    rw [atLabels]
    simp [code, Instruction.execute, decData]
  | write d b =>
    apply runs_one
    rw [atLabels]; rfl
  | discard d =>
    apply runs_one
    rw [atLabels]; rfl
  | @rewind_empty d hd =>
    apply runs_one
    rw [atLabels]
    simp [code, Instruction.execute, hd]
    cases d; simp_all
  | @rewind_cons d e n b rest hd he ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p labels exit atLabels)
    rw [atLabels]
    simp [code, entry, Instruction.execute, backData, hd]
  | @seq a b d e f n m h h' ih ih' =>
    exact Runs.trans
      (ih p (fun l => labels (.inl l)) (labels (.inr b.entry)) (fun l => atLabels (.inl l)))
      (ih' p (fun l => labels (.inr l)) exit (fun l => atLabels (.inr l)))
  | @test_zero r a b d e n hr h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inl l))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, hr]
  | @test_pos r a b d e n hr h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inr l))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, hr]
  | @read_one a b c d e n rest hin h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inl l))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, readData, hin]
  | @read_zero a b c d e n rest hin h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inr (.inl l)))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, readData, hin]
  | @read_empty a b c d e n hin h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inr (.inr l)))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, readData, hin]
  | @loop_zero r b d hr =>
    apply runs_one
    rw [atLabels]
    simp [code, entry, Instruction.execute, hr]
    rw [← hr, Function.update_eq_self]
  | @loop_pos r b d e f n m hr h h' ih ih' =>
    refine Runs.trans (Runs.trans (runs_one p _ _ _ _ ?_)
      (ih p (fun l => labels (.inr l)) (labels (.inl ())) (fun l => atLabels (.inr l))))
        (ih' p labels exit atLabels)
    rw [atLabels]
    simp [code, entry, Instruction.execute, decData, hr]
end Command
end OptimalMaxCut.CounterMachine

namespace OptimalMaxCut.CounterMachine
open Turing
variable {R L : Type} [DecidableEq R]

 theorem advance_simulation (p : L → Instruction R L) (a : Option (Configuration R L)) :
    (a.map embed).bind (TM2.step (fun l => (p l).code)) = (advance p a).map embed := by
  cases a with
  | none => rfl
  | some c => exact step_simulation p c

 theorem iterate_simulation (p : L → Instruction R L) (n : ℕ)
    (a : Option (Configuration R L)) :
    (fun a => a.bind (TM2.step (fun l => (p l).code)))^[n] (a.map embed) =
      ((advance p)^[n] a).map embed := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, advance_simulation, Function.iterate_succ_apply']

namespace Command

abbrev FinalLabel (c : Command R) := c.Label ⊕ Unit

def finalCode (c : Command R) : c.FinalLabel → Instruction R c.FinalLabel
  | .inl l => c.code Sum.inl (.inr ()) l
  | .inr _ => .halt

def initial (input : List Bool) : Data R :=
  ⟨fun _ => 0, input, [], []⟩

noncomputable def finiteMachine [Fintype R] (c : Command R) : FinTM2 :=
  machine c.finalCode (.inl c.entry)

 theorem finiteMachine_initial [Fintype R] (c : Command R) (input : List Bool) :
    initList c.finiteMachine input = embed ⟨initial input, some (.inl c.entry)⟩ := by
  unfold initList
  congr 1
  funext k
  cases k <;> simp [finiteMachine, machine, tapes, initial]
  rfl

/-- Every derived structured evaluation is an actual finite-alphabet execution,
including the final halt transition. No arithmetic oracle is added. -/
 noncomputable def machine_run [Fintype R] {c : Command R} {input : List Bool} {out : Data R} {n : ℕ}
    (h : Evaluates c (initial input) out n) :
    StateTransition.EvalsToInTime c.finiteMachine.step (initList c.finiteMachine input)
      (some (embed ⟨out, none⟩)) (n + 1) := by
  have hr := trace h c.finalCode Sum.inl (.inr ()) (fun _ => rfl)
  have hi := iterate_simulation c.finalCode n (atCfg (.inl c.entry) (initial input))
  have hit : (fun a : Option (Configuration R c.FinalLabel) => advance c.finalCode a)^[n + 1]
      (atCfg (.inl c.entry) (initial input)) = some ⟨out, none⟩ := by
    rw [Function.iterate_succ_apply', hr]
    rfl
  refine ⟨⟨n + 1, ?_⟩, le_rfl⟩
  rw [finiteMachine_initial]
  change (fun a => a.bind (TM2.step (fun l => (c.finalCode l).code)))^[n + 1]
      ((atCfg (.inl c.entry) (initial input)).map embed) = _
  rw [iterate_simulation, hit]
  rfl

 theorem finiteMachine_finite_alphabet [Fintype R] (c : Command R)
    (k : c.finiteMachine.K) : Finite (c.finiteMachine.Γ k) := inferInstanceAs (Finite Bool)

end Command
end OptimalMaxCut.CounterMachine

namespace OptimalMaxCut.CounterMachine
open scoped BigOperators
variable {R : Type} [DecidableEq R]

namespace Data

def set (d : Data R) (r : R) (v : ℕ) : Data R :=
  { d with reg := Function.update d.reg r v }

@[simp] theorem set_self (d : Data R) (r : R) : d.set r (d.reg r) = d := by
  simp [set]

@[simp] theorem set_set (d : Data R) (r : R) (v w : ℕ) :
    (d.set r v).set r w = d.set r w := by simp [set]

@[simp] theorem set_reg_same (d : Data R) (r : R) (v : ℕ) :
    (d.set r v).reg r = v := by simp [set]

@[simp] theorem set_reg_ne (d : Data R) (r s : R) (v : ℕ) (h : s ≠ r) :
    (d.set r v).reg s = d.reg s := by simp [set, h]

 theorem set_comm (d : Data R) (r s : R) (v w : ℕ) (h : r ≠ s) :
    (d.set r v).set s w = (d.set s w).set r v := by
  simp only [set]
  congr 1
  exact Function.update_comm h v w d.reg

end Data

namespace Command

def clear (r : R) : Command R := .loop r .skip

def move (r s : R) : Command R := .loop r (.inc s)

 theorem clear_evaluates (d : Data R) (r : R) :
    Evaluates (clear r) d (d.set r 0) (2 * d.reg r + 1) := by
  generalize hn : d.reg r = n
  induction n generalizing d with
  | zero =>
    have hs : d.set r 0 = d := by rw [← hn, Data.set_self]
    simpa [clear, hs] using (Evaluates.loop_zero (b := .skip) hn)
  | succ n ih =>
    have hr : d.reg r ≠ 0 := by omega
    have hd : (decData d r).reg r = n := by simp [decData, hn]
    have he := ih (decData d r) hd
    have hf : (decData d r).set r 0 = d.set r 0 := by simp [decData, Data.set]
    have ht : 1 + 1 + (2 * n + 1) = 2 * (n + 1) + 1 := by omega
    simpa only [clear, hf, ht] using
      (Evaluates.loop_pos hr (Evaluates.skip (decData d r)) he)

 theorem move_evaluates (d : Data R) (r s : R) (hrs : r ≠ s) :
    Evaluates (move r s) d ((d.set r 0).set s (d.reg s + d.reg r))
      (2 * d.reg r + 1) := by
  generalize hn : d.reg r = n
  induction n generalizing d with
  | zero =>
    have hz : d.set r 0 = d := by rw [← hn, Data.set_self]
    simpa [move, hz] using (Evaluates.loop_zero (b := .inc s) hn)
  | succ n ih =>
    have hr : d.reg r ≠ 0 := by omega
    let e := incData (decData d r) s
    have er : e.reg r = n := by simp [e, incData, decData, hrs, hn]
    have es : e.reg s = d.reg s + 1 := by simp [e, incData, decData, Ne.symm hrs]
    have he := ih e er
    have hf : (e.set r 0).set s (e.reg s + n) =
        (d.set r 0).set s (d.reg s + (n + 1)) := by
      simp only [es]
      have hc : e.set r 0 = (d.set r 0).set s (d.reg s + 1) := by
        dsimp [e, incData, decData, Data.set]
        congr 1
        ext t
        by_cases ht : t = r <;> by_cases hs : t = s <;> simp_all
      rw [hc, Data.set_set]
      congr 1
      omega
    have ht : 1 + 1 + (2 * n + 1) = 2 * (n + 1) + 1 := by omega
    simpa only [move, hf, ht] using (Evaluates.loop_pos hr (Evaluates.inc (decData d r) s) he)

/-- A definite cutoff clock for an actually terminating command, not an
assumed machine-computability predicate. -/
def Within (c : Command R) (d e : Data R) (B : ℕ) : Prop :=
  ∃ n ≤ B, Evaluates c d e n

 theorem Within.seq {a b : Command R} {d e f : Data R} {B C : ℕ}
    (h : Within a d e B) (h' : Within b e f C) : Within (.seq a b) d f (B + C) := by
  obtain ⟨n, hn, he⟩ := h
  obtain ⟨m, hm, hf⟩ := h'
  exact ⟨n + m, Nat.add_le_add hn hm, Evaluates.seq he hf⟩

 theorem Within.mono {c : Command R} {d e : Data R} {B C : ℕ}
    (h : Within c d e B) (hBC : B ≤ C) : Within c d e C := by
  obtain ⟨n, hn, he⟩ := h
  exact ⟨n, hn.trans hBC, he⟩

end Command
end OptimalMaxCut.CounterMachine

namespace OptimalMaxCut.CounterMachine
open scoped BigOperators
variable {R : Type} [DecidableEq R]

omit [DecidableEq R] in
@[ext] theorem Data.ext {d e : Data R} (hr : d.reg = e.reg)
    (hi : d.input = e.input) (hb : d.backup = e.backup) (ho : d.output = e.output) : d = e := by
  cases d; cases e; simp_all

namespace Command

theorem Within.loop (r : R) (b : Command R) (state : ℕ → Data R) (n B : ℕ)
    (hr : ∀ i ≤ n, (state i).reg r = i)
    (hb : ∀ i < n, Within b (decData (state (i+1)) r) (state i) B) :
    Within (.loop r b) (state n) (state 0) (n * (B + 1) + 1) := by
  induction n with
  | zero => exact ⟨1, by omega, Evaluates.loop_zero (hr 0 le_rfl)⟩
  | succ n ih =>
    obtain ⟨a, ha, ea⟩ := hb n (by omega)
    obtain ⟨b', hb', eb⟩ := ih (fun i hi => hr i (by omega)) (fun i hi => hb i (by omega))
    refine ⟨1 + a + b', ?_, Evaluates.loop_pos (by rw [hr (n+1) le_rfl]; omega) ea eb⟩
    nlinarith

 theorem Within.inc (d : Data R) (r : R) : Within (.inc r) d (incData d r) 1 :=
  ⟨1, le_rfl, Evaluates.inc d r⟩
 theorem Within.dec (d : Data R) (r : R) : Within (.dec r) d (decData d r) 1 :=
  ⟨1, le_rfl, Evaluates.dec d r⟩
 theorem Within.skip (d : Data R) : Within (.skip : Command R) d d 1 :=
  ⟨1, le_rfl, Evaluates.skip d⟩
 theorem Within.clear (d : Data R) (r : R) :
    Within (clear r) d (d.set r 0) (2*d.reg r+1) :=
  ⟨_, le_rfl, clear_evaluates d r⟩
 theorem Within.move (d : Data R) (r s : R) (h : r ≠ s) :
    Within (move r s) d ((d.set r 0).set s (d.reg s+d.reg r)) (2*d.reg r+1) :=
  ⟨_, le_rfl, move_evaluates d r s h⟩

/-- Copy without destruction using a disjoint zeroed backup register. -/
def copy (r s t : R) : Command R :=
  .seq (.loop r (.seq (.inc s) (.inc t))) (move t r)

 theorem copy_evaluates (d : Data R) (r s t : R)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (ht : d.reg t = 0) :
    Within (copy r s t) d (d.set s (d.reg s + d.reg r)) (5*d.reg r+2) := by
  let n := d.reg r
  let state : ℕ → Data R := fun i => ((d.set r i).set s (d.reg s+n-i)).set t (n-i)
  have hn : state n = d := by
    ext u <;> simp [state, Data.set, n]
    by_cases hu : u = r <;> by_cases hs : u = s <;> by_cases ht' : u = t <;> simp_all
  have hloop : Within (.loop r (.seq (.inc s) (.inc t))) (state n) (state 0) (n*3+1) := by
    apply Within.loop r _ state n 2
    · intro i hi; simp [state, Data.set, hrs, hrt]
    · intro i hi
      have he := (Within.inc (decData (state (i+1)) r) s).seq
        (Within.inc (incData (decData (state (i+1)) r) s) t)
      have hout : incData (incData (decData (state (i+1)) r) s) t = state i := by
        ext u <;> simp only [incData, decData, state, Data.set]
        by_cases hu : u = r <;> by_cases hs : u = s <;> by_cases ht' : u = t <;>
          simp [hu, hs, ht', hrs, hrt, hst, Ne.symm hrs, Ne.symm hrt, Ne.symm hst] <;> omega
      simpa only [hout] using he
  rw [hn] at hloop
  have hm := Within.move (state 0) t r (Ne.symm hrt)
  have hout : ((state 0).set t 0).set r ((state 0).reg r + (state 0).reg t) =
      d.set s (d.reg s + d.reg r) := by
    ext u <;> simp only [state, Data.set]
    by_cases hu : u = r <;> by_cases hs : u = s <;> by_cases ht' : u = t <;>
      simp [hu, hs, ht', hrs, hrt, hst, Ne.symm hrs, Ne.symm hrt, Ne.symm hst, ht, n]
  have ht' : (state 0).reg t = n := by simp [state, Data.set]
  have h := hloop.seq hm
  rw [hout, ht'] at h
  convert h using 1 <;> dsimp [copy, n] ; omega

def mulAdd (count source target backup : R) : Command R :=
  .loop count (copy source target backup)

 theorem mulAdd_evaluates (d : Data R) (c r s t : R)
    (hcr : c ≠ r) (hcs : c ≠ s) (hct : c ≠ t)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (ht : d.reg t = 0) :
    Within (mulAdd c r s t) d ((d.set c 0).set s (d.reg s+d.reg c*d.reg r))
      (d.reg c*(5*d.reg r+3)+1) := by
  let n := d.reg c
  let state : ℕ → Data R := fun i => (d.set c i).set s (d.reg s+(n-i)*d.reg r)
  have hn : state n = d := by
    simp [state, n]
  have hloop : Within (.loop c (copy r s t)) (state n) (state 0)
      (n*(5*d.reg r+3)+1) := by
    apply Within.loop c _ state n (5*d.reg r+2)
    · intro i hi; simp [state, Data.set, hcs]
    · intro i hi
      have hr' : (decData (state (i+1)) c).reg r = d.reg r := by
        simp [state, decData, Data.set, Ne.symm hcr, hrs]
      have ht' : (decData (state (i+1)) c).reg t = 0 := by
        simp [state, decData, Data.set, Ne.symm hct, Ne.symm hst, ht]
      have h := copy_evaluates (decData (state (i+1)) c) r s t hrs hrt hst ht'
      rw [hr'] at h
      have hout : (decData (state (i+1)) c).set s
          ((decData (state (i+1)) c).reg s + d.reg r) = state i := by
        have hh : (n-(i+1))*d.reg r+d.reg r = (n-i)*d.reg r := by
          have : n-i = n-(i+1)+1 := by omega
          rw [this, Nat.add_mul, Nat.one_mul]
        ext u <;> simp only [decData, state, Data.set]
        by_cases hu : u = c <;> by_cases hs : u = s <;>
          simp [hu, hs, hcs, Ne.symm hcs, Nat.add_assoc] ; omega
      simpa only [hout] using h
  simpa [mulAdd, hn, state, n] using hloop

end Command
end OptimalMaxCut.CounterMachine

end

end OAI
