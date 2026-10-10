import Mathlib
import OAI.Computability.MaxCut.Encoding.InputEncoding
import OAI.Computability.MaxCut.Machines.Runtime
import OAI.Computability.MaxCut.Encoding.NameCompaction

namespace OAI

namespace MaxCutGames.BinaryFormula

open MaxCutGames.Foundations

def sourceNames (F : Formula) : List Nat :=
  F.clauses.flatMap clauseNames

/-- Explicit list of occurring names, with duplicates removed. The list lengths
depend only on occurrences; no interval of natural-number names is enumerated. -/
def activeNames (F : Formula) : List Nat :=
  (sourceNames F).eraseDups

theorem literal_mem_active (F : Formula) (c : Clause)
    (hc : c ∈ F.clauses) (i : Fin 3) : (c)[i].name ∈ activeNames F := by
  simp only [activeNames, List.mem_eraseDups]
  apply List.mem_flatMap.mpr
  refine ⟨c, hc, ?_⟩
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> simp [clauseNames]

def compactIndex (F : Formula) (v : Nat)
    (hv : v ∈ activeNames F) : Fin (activeNames F).length :=
  ⟨(activeNames F).idxOf v, List.idxOf_lt_length_iff.mpr hv⟩

def decodeName (F : Formula) (v : Fin (activeNames F).length) : Nat :=
  (activeNames F)[v.val]

def compactLiteral (F : Formula) (l : Literal)
    (hl : l.name ∈ activeNames F) : Target.Literal (activeNames F).length :=
  ⟨compactIndex F l.name hl, l.positive⟩

def compactClause (F : Formula) (c : Clause)
    (hc : c ∈ F.clauses) : Target.Clause (activeNames F).length :=
  #v[compactLiteral F (c)[0] (literal_mem_active F c hc 0),
    compactLiteral F (c)[1] (literal_mem_active F c hc 1),
    compactLiteral F (c)[2] (literal_mem_active F c hc 2)]

def compactClauses (F : Formula) : List (Target.Clause (activeNames F).length) :=
  F.clauses.attach.map (fun c => compactClause F c.val c.property)

def dense (F : Formula) : Target.Formula where
  «variables» := (activeNames F).length
  clauses := compactClauses F

def restrictAssignment (F : Formula) (A : Nat → Bool) :
    Fin (activeNames F).length → Bool := fun v => A (decodeName F v)

def extendAssignment (F : Formula) (B : Fin (activeNames F).length → Bool)
    (v : Nat) : Bool :=
  if hv : v ∈ activeNames F then B (compactIndex F v hv) else false

@[simp] theorem decode_compactIndex (F : Formula) (v : Nat)
    (hv : v ∈ activeNames F) : decodeName F (compactIndex F v hv) = v := by
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hv)

/-- Distinct occurring names remain distinct. Repeated occurrences of one name
use the same index, since the proof argument of `compactIndex` is irrelevant. -/
theorem compactIndex_injective (F : Formula) (u v : Nat)
    (hu : u ∈ activeNames F) (hv : v ∈ activeNames F)
    (h : compactIndex F u hu = compactIndex F v hv) : u = v := by
  have decoded := congrArg (decodeName F) h
  simpa only [decode_compactIndex] using decoded

@[simp] theorem compactLiteral_positive (F : Formula) (l : Literal)
    (hl : l.name ∈ activeNames F) : (compactLiteral F l hl).positive = l.positive := rfl

@[simp] theorem eval_compact_restrict (F : Formula) (c : Clause)
    (hc : c ∈ F.clauses) (A : Nat → Bool) :
    (compactClause F c hc).eval (restrictAssignment F A) = c.eval A := by
  simp [compactClause, compactLiteral, Target.Clause.eval, Target.Literal.eval,
    Clause.eval, Literal.eval, restrictAssignment, decode_compactIndex]

@[simp] theorem eval_compact_extend (F : Formula) (c : Clause)
    (hc : c ∈ F.clauses) (B : Fin (activeNames F).length → Bool) :
    (compactClause F c hc).eval B = c.eval (extendAssignment F B) := by
  have h₀ : (c)[0].name ∈ activeNames F := literal_mem_active F c hc 0
  have h₁ : (c)[1].name ∈ activeNames F := literal_mem_active F c hc 1
  have h₂ : (c)[2].name ∈ activeNames F := literal_mem_active F c hc 2
  simp [compactClause, compactLiteral, Target.Clause.eval, Target.Literal.eval,
    Clause.eval, Literal.eval, extendAssignment, h₀, h₁, h₂] ; rfl

def evaluationList (F : Formula) (A : Nat → Bool) : List Bool :=
  F.clauses.map (fun c => c.eval A)

/-- Evaluation lists retain every clause occurrence, so this is stronger than
merely preserving satisfiability or the set of distinct clauses. -/
theorem evaluationList_restrict (F : Formula) (A : Nat → Bool) :
    PCP.NameCompaction.evaluationList (dense F) (restrictAssignment F A) =
      evaluationList F A := by
  simp only [PCP.NameCompaction.evaluationList, evaluationList, dense, compactClauses,
    List.map_map]
  simpa only [Function.comp_def, eval_compact_restrict] using
    PCP.NameCompaction.map_attach_val F.clauses (fun c => c.eval A)

theorem evaluationList_extend (F : Formula) (B : Fin (dense F).«variables» → Bool) :
    PCP.NameCompaction.evaluationList (dense F) B =
      evaluationList F (extendAssignment F B) := by
  simp only [PCP.NameCompaction.evaluationList, evaluationList, dense, compactClauses,
    List.map_map]
  change F.clauses.attach.map (fun c => (compactClause F c.val c.property).eval B) = _
  calc
    _ = F.clauses.attach.map (fun c => c.val.eval (extendAssignment F B)) := by
      apply List.map_congr_left
      intro c _
      exact eval_compact_extend F c.val c.property B
    _ = _ := PCP.NameCompaction.map_attach_val F.clauses
      (fun c => c.eval (extendAssignment F B))

def failedCount (F : Formula) (A : Nat → Bool) : Nat :=
  (evaluationList F A).count false

theorem failedCount_restrict (F : Formula) (A : Nat → Bool) :
    PCP.NameCompaction.failedCount (dense F) (restrictAssignment F A) = failedCount F A := by
  simp only [PCP.NameCompaction.failedCount, failedCount, evaluationList_restrict]

theorem failedCount_extend (F : Formula) (B : Fin (dense F).«variables» → Bool) :
    PCP.NameCompaction.failedCount (dense F) B = failedCount F (extendAssignment F B) := by
  simp only [PCP.NameCompaction.failedCount, failedCount, evaluationList_extend]

theorem clauseNames_flat_length (cs : List Clause) :
    (cs.flatMap clauseNames).length = 3 * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, clauseNames,
      List.length_cons, List.length_nil, ih]
    omega

@[simp] theorem dense_clause_count (F : Formula) :
    (dense F).clauses.length = F.clauses.length := by
  simp [dense, compactClauses]

/-- No greatest-name bound occurs: even very large, sparsely used names yield
at most three dense «variables» per explicitly listed clause. -/
theorem dense_variable_bound (F : Formula) :
    (dense F).«variables» ≤ 3 * F.clauses.length := by
  have h := PCP.NameCompaction.length_eraseDups_le (sourceNames F)
  simpa only [sourceNames, clauseNames_flat_length, dense, activeNames] using h

theorem dense_completeness (F : Formula) (hs : F.Satisfiable) :
    (dense F).Satisfiable := by
  rcases hs with ⟨A, hA⟩
  refine ⟨restrictAssignment F A, ?_⟩
  intro d hd
  change d ∈ F.clauses.attach.map (fun c => compactClause F c.val c.property) at hd
  rcases List.mem_map.mp hd with ⟨c, _, rfl⟩
  exact (eval_compact_restrict F c.val c.property A).trans (hA c.val c.property)

theorem dense_reflects (F : Formula) (hs : (dense F).Satisfiable) : F.Satisfiable := by
  rcases hs with ⟨B, hB⟩
  refine ⟨extendAssignment F B, ?_⟩
  intro c hc
  have hm : compactClause F c hc ∈ (dense F).clauses := by
    change _ ∈ F.clauses.attach.map (fun d => compactClause F d.val d.property)
    exact List.mem_map.mpr ⟨⟨c, hc⟩, by simp, rfl⟩
  rw [← eval_compact_extend F c hc B]
  exact hB _ hm

theorem dense_satisfiable_iff (F : Formula) :
    (dense F).Satisfiable ↔ F.Satisfiable :=
  ⟨dense_reflects F, dense_completeness F⟩

theorem dense_preserves_gap (F : Formula) (a b : Nat)
    (gap : ∀ A, a * F.clauses.length ≤ b * failedCount F A)
    (B : Fin (dense F).«variables» → Bool) :
    a * (dense F).clauses.length ≤ b * PCP.NameCompaction.failedCount (dense F) B := by
  rw [dense_clause_count, failedCount_extend]
  exact gap (extendAssignment F B)

/-- Size of the reused dense formula encoding, bounded only by the number of
explicit clause occurrences. This does not assert a binary input parser or a
running-time bound for sparse-to-dense conversion. -/
theorem dense_encoding_bound (F : Formula) :
    (Complexity.formulaBits (dense F)).length ≤
      9 * F.clauses.length * F.clauses.length + 10 * F.clauses.length + 2 := by
  have enc := Complexity.formulaBits_length_le (dense F)
  rw [dense_clause_count] at enc
  have active := dense_variable_bound F
  have h₁ := Nat.add_le_add_right active (F.clauses.length + 2)
  have h₂ := Nat.mul_le_mul_left F.clauses.length
    (Nat.mul_le_mul_left 3 (Nat.add_le_add_right active 2))
  have total := Nat.add_le_add h₁ h₂
  have polynomial : 3 * F.clauses.length + (F.clauses.length + 2) +
      F.clauses.length * (3 * (3 * F.clauses.length + 2)) =
      9 * F.clauses.length * F.clauses.length + 10 * F.clauses.length + 2 := by
    ring
  rw [polynomial] at total
  omega

end MaxCutGames.BinaryFormula

/-!
An explicit ordinary-binary codec for sparse-name three-literal CNF.

A natural name uses its canonical little-endian binary digits. Each payload
digit b is represented by the pair `true,b`; `false` terminates the name.
Zero has the empty payload and therefore the one-bit encoding `[false]`.
A literal is its sign bit followed by its name. A clause contains three literal
encodings. A formula contains `true` followed by each clause, then one final
`false`. There is no unary expansion of a variable name, declared variable
universe, or deduplication of literal or clause occurrences.

The parser rejects noncanonical name payloads, incomplete literals/clauses, and
trailing input. The input length is within a fixed factor of the total ordinary
binary name lengths plus signs and clause framing. Machine correspondence and
runtime are proved separately; these output-size bounds are not time bounds.
-/

namespace MaxCutGames.BinaryEncoding

open BinaryFormula

/-- The existing dense unary output is polynomial in this ordinary binary
input length. This remains an output-size theorem, not a runtime certificate. -/
theorem dense_encoding_bound (formula : Formula) :
    (MaxCutGames.Foundations.Complexity.formulaBits (dense formula)).length ≤
      9 * (formulaBits formula).length * (formulaBits formula).length +
      10 * (formulaBits formula).length + 2 := by
  have h := BinaryFormula.dense_encoding_bound formula
  have hm : formula.clauses.length ≤ (formulaBits formula).length :=
    (clauses_length_lt_bits formula.clauses).le
  have hsq := Nat.mul_self_le_mul_self hm
  nlinarith

end MaxCutGames.BinaryEncoding

/-!
# A destructive equality test on two actual Bool stacks

Each loop transition pops both stacks and compares only the two finite head
registers. A sticky mismatch flag makes the loop continue after disagreement.
The final empty/empty test selects an equal or different continuation and resets
all comparison registers. The ambient state and every other tape are preserved.
-/

namespace MaxCutGames.Foundations.Complexity.MachineCompare

open Turing
open MaxCutGames.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (K : Type) : K → Type := fun _ => Bool
abbrev State (σ : Type) := σ × Bool × Option Bool × Option Bool

/-- An optional continuation, without reading or writing any tape. -/
def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

/-- Clear both head registers and the mismatch flag after choosing the exit. -/
def finish (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  .load (fun state => (state.1, false, none, none)) (exitAt exit)

/-- The only comparison performed by the program is on two `Option Bool` heads.
In particular, no statement is given a whole-list equality oracle. -/
def loop (left right : K) (loopLabel : Λ) (equalExit differentExit : Option Λ) :
    TM2.Stmt (Alphabet K) Λ (State σ) :=
  .pop left (fun state head => (state.1, state.2.1, head, state.2.2.2))
    (.pop right (fun state head => (state.1, state.2.1, state.2.2.1, head))
      (.branch (fun state => state.2.2.1.isNone && state.2.2.2.isNone)
        (.branch (fun state => state.2.1) (finish differentExit) (finish equalExit))
        (.load (fun state =>
          (state.1, state.2.1 || decide (state.2.2.1 ≠ state.2.2.2), none, none))
          (.goto fun _ => loopLabel))))

/-- Specification-only outcome, also recording an earlier mismatch. -/
def mismatch (flag : Bool) (leftWord rightWord : List Bool) : Bool :=
  flag || decide (leftWord ≠ rightWord)

@[simp] theorem mismatch_nil_nil (flag : Bool) : mismatch flag [] [] = flag := by
  simp [mismatch]

@[simp] theorem mismatch_nil_cons (flag head : Bool) (tail : List Bool) :
    mismatch flag [] (head :: tail) = true := by simp [mismatch]

@[simp] theorem mismatch_cons_nil (flag head : Bool) (tail : List Bool) :
    mismatch flag (head :: tail) [] = true := by simp [mismatch]

@[simp] theorem mismatch_true (leftWord rightWord : List Bool) :
    mismatch true leftWord rightWord = true := by simp [mismatch]

theorem mismatch_cons (flag leftHead rightHead : Bool) (leftTail rightTail : List Bool) :
    mismatch (flag || decide (leftHead ≠ rightHead)) leftTail rightTail =
      mismatch flag (leftHead :: leftTail) (rightHead :: rightTail) := by
  cases flag <;> cases leftHead <;> cases rightHead <;> simp [mismatch]

@[simp] theorem stepAux_exitAt (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (exitAt exit) state tapes = ⟨exit, state, tapes⟩ := by
  cases exit <;> rfl

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (finish exit) state tapes =
      ⟨exit, (state.1, false, none, none), tapes⟩ := by
  simp [finish, TM2.stepAux]

private theorem update_left_inline_MachineCompare (left right : K) (distinct : left ≠ right)
    (base : K → List Bool) (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) left replacement =
      tapesAt left right base replacement rightWord := by
  funext k
  by_cases hl : k = left
  · subst k
    simp [tapesAt, distinct]
  · by_cases hr : k = right
    · subst k
      simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hl, hr]

private theorem update_right_inline_MachineCompare (left right : K) (base : K → List Bool)
    (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) right replacement =
      tapesAt left right base leftWord replacement := by
  simp [tapesAt]

theorem step_empty (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] []⟩ =
      some ⟨if flag then differentExit else equalExit, (ambient, false, none, none),
        tapesAt left right base [] []⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base [] [])) = _
  rw [atLoop]
  cases flag <;>
    simp [loop, TM2.stepAux, distinct, update_left_inline_MachineCompare, update_right_inline_MachineCompare]

theorem step_nil_cons (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] (head :: tail)⟩ =
      some ⟨some loopLabel, (ambient, true, none, none), tapesAt left right base [] tail⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base [] (head :: tail))) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left_inline_MachineCompare, update_right_inline_MachineCompare]

theorem step_cons_nil (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base (head :: tail) []⟩ =
      some ⟨some loopLabel, (ambient, true, none, none), tapesAt left right base tail []⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base (head :: tail) [])) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left_inline_MachineCompare, update_right_inline_MachineCompare]

theorem step_cons_cons (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftHead rightHead : Bool) (leftTail rightTail : List Bool)
    (ambient : σ) (flag : Bool) (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base (leftHead :: leftTail) (rightHead :: rightTail)⟩ =
      some ⟨some loopLabel,
        (ambient, flag || decide (leftHead ≠ rightHead), none, none),
        tapesAt left right base leftTail rightTail⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base (leftHead :: leftTail) (rightHead :: rightTail))) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left_inline_MachineCompare, update_right_inline_MachineCompare]

private theorem trace_left_empty_inline_MachineCompare (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (rightWord : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] rightWord⟩) =
      some ⟨if mismatch flag [] rightWord then differentExit else equalExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  induction rightWord generalizing flag leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, mismatch_nil_nil] using
      step_empty left right distinct loopLabel equalExit differentExit program atLoop base
        ambient flag leftRegister rightRegister
  | cons head tail ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
      (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] (head :: tail)⟩) = _
    rw [step_nil_cons left right distinct loopLabel equalExit differentExit program atLoop]
    simpa only [mismatch_true, mismatch_nil_cons] using ih true none none

/-- The exact trace with a possibly pre-existing mismatch. Every input symbol
is consumed even when disagreement has already been detected. -/
theorem compareTrace_flag (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨if mismatch flag leftWord rightWord then differentExit else equalExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  induction leftWord generalizing rightWord flag leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_max] using
      trace_left_empty_inline_MachineCompare left right distinct loopLabel equalExit differentExit program atLoop
        base rightWord ambient flag leftRegister rightRegister
  | cons head tail ih =>
    cases rightWord with
    | nil =>
      rw [List.length_cons, List.length_nil, Nat.max_zero, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
        (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
          tapesAt left right base (head :: tail) []⟩) = _
      rw [step_cons_nil left right distinct loopLabel equalExit differentExit program atLoop]
      simpa only [List.length_nil, Nat.max_zero, mismatch_true, mismatch_cons_nil] using
        ih [] true none none
    | cons rightHead rightTail =>
      rw [List.length_cons, List.length_cons, Nat.succ_max_succ, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[max tail.length rightTail.length + 1]
        (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
          tapesAt left right base (head :: tail) (rightHead :: rightTail)⟩) = _
      rw [step_cons_cons left right distinct loopLabel equalExit differentExit program atLoop]
      simpa only [mismatch_cons] using
        ih rightTail (flag || decide (head ≠ rightHead)) none none

/-- With a clear initial flag, the final continuation tests equality of the
two complete original words. Both tapes and all comparison registers are empty. -/
theorem compareTrace (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, false, leftRegister, rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨if leftWord = rightWord then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  have h := compareTrace_flag left right distinct loopLabel equalExit differentExit program
    atLoop base leftWord rightWord ambient false leftRegister rightRegister
  by_cases heq : leftWord = rightWord <;> simpa [mismatch, heq] using h

theorem compareTrace_fromTapes (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max (base left).length (base right).length + 1]
      (some ⟨some loopLabel, (ambient, false, leftRegister, rightRegister), base⟩) =
      some ⟨if base left = base right then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  simpa only [tapesAt_self] using
    compareTrace left right distinct loopLabel equalExit differentExit program atLoop base
      (base left) (base right) ambient leftRegister rightRegister

/-- The final tape family agrees with the original at every unselected tape. -/
theorem drained_other (left right k : K) (notLeft : k ≠ left) (notRight : k ≠ right)
    (base : K → List Bool) : tapesAt left right base [] [] k = base k :=
  tapesAt_other left right k notLeft notRight base [] []

/-- An actual timed execution witness, with the exact stored transition count. -/
def compareInTime (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, false, leftRegister, rightRegister), base⟩
      (some ⟨if base left = base right then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩)
      (max (base left).length (base right).length + 1) where
  steps := max (base left).length (base right).length + 1
  evals_in_steps := compareTrace_fromTapes left right distinct loopLabel equalExit differentExit
    program atLoop base ambient leftRegister rightRegister
  steps_le_m := Nat.le_refl _

@[simp] theorem compareInTime_steps (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    (compareInTime left right distinct loopLabel equalExit differentExit program atLoop base
      ambient leftRegister rightRegister).steps =
        max (base left).length (base right).length + 1 := rfl

end MaxCutGames.Foundations.Complexity.MachineCompare

namespace MaxCutGames.BinaryNameMachine

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer

def frame : List Bool → List Bool
  | [] => [false]
  | bit :: bits => true :: bit :: frame bits

def finalDigit : List Bool → Option Bool → Option Bool
  | [], previous => previous
  | bit :: bits, _ => finalDigit bits (some bit)

def canonical (bits : List Bool) : Bool := (finalDigit bits none).getD true

structure Result where
  accepted : Bool
  remaining : List Bool
  reversedPayload : List Bool
  deriving DecidableEq

/-- A specification with the same one- or two-symbol cases as the program. -/
def scanSpec : List Bool → List Bool → Option Bool → Result
  | [], acc, _ => ⟨false, [], acc⟩
  | false :: rest, acc, last => ⟨last.getD true, rest, acc⟩
  | [true], acc, _ => ⟨false, [], acc⟩
  | true :: bit :: rest, acc, _ => scanSpec rest (bit :: acc) (some bit)

def steps : List Bool → Nat
  | true :: _ :: rest => steps rest + 1
  | _ => 1

theorem steps_le (input : List Bool) : steps input ≤ input.length + 1 := by
  induction input using List.twoStepInduction with
  | nil => simp [steps]
  | singleton bit => cases bit <;> simp [steps]
  | cons_cons flag bit rest ih _ =>
      cases flag <;> simp only [steps, List.length_cons]
      · omega
      · omega

@[simp] theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => simp [frame]
  | cons bit bits ih => simp only [frame, List.length_cons, ih]; omega

theorem scanSpec_frame (bits suffix acc : List Bool) (last : Option Bool) :
    scanSpec (frame bits ++ suffix) acc last =
      ⟨(finalDigit bits last).getD true, suffix, bits.reverse ++ acc⟩ := by
  induction bits generalizing acc last with
  | nil => simp [frame, scanSpec, finalDigit]
  | cons bit bits ih =>
      simpa [frame, scanSpec, finalDigit, List.reverse_cons, List.append_assoc] using
        ih (bit :: acc) (some bit)

@[simp] theorem steps_frame (bits suffix : List Bool) :
    steps (frame bits ++ suffix) = bits.length + 1 := by
  induction bits with
  | nil => simp [frame, steps]
  | cons bit bits ih => simp [frame, steps, ih]

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool × Option Bool

def clean (ambient : A) : State A := (ambient, none, none)

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1) (exitAt exit)

/-- Only the finite head and final-digit registers are inspected by branches. -/
def scan (source destination : K) (again : Λ) (accepted rejected : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .pop source (fun state head => (state.1, state.2.1, head))
    (.branch (fun state => state.2.2.isNone)
      (finish rejected)
      (.branch (fun state => state.2.2.getD false)
        (.pop source (fun state head => (state.1, state.2.1, head))
          (.branch (fun state => state.2.2.isSome)
            (.push destination (fun state => state.2.2.getD false)
              (.load (fun state => (state.1, state.2.2, none))
                (.goto fun _ => again)))
            (finish rejected)))
        (.branch (fun state => state.2.1.getD true)
          (finish accepted) (finish rejected))))

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A)
    (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1, base⟩ := by
  cases exit <;> rfl

private theorem update_source_inline_MachineBinaryNameMachine (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) source replacement =
      tapesAt source destination base replacement output := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapesAt, distinct]
  · by_cases hd : k = destination
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

private theorem update_destination_inline_MachineBinaryNameMachine (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) destination replacement =
      tapesAt source destination base input replacement := by
  simp [tapesAt]

variable (source destination : K) (distinct : source ≠ destination)
variable (again : Λ) (accepted rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atScan : program again = scan source destination again accepted rejected)
variable (base : K → List Bool) (ambient : A)

include distinct atScan

theorem step_empty (output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register), tapesAt source destination base [] output⟩ =
      some ⟨rejected, clean ambient, tapesAt source destination base [] output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source_inline_MachineBinaryNameMachine]

theorem step_end (rest output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register),
        tapesAt source destination base (false :: rest) output⟩ =
      some ⟨if last.getD true then accepted else rejected, clean ambient,
        tapesAt source destination base rest output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  cases h : last.getD true <;>
    simp [scan, TM2.stepAux, distinct, update_source_inline_MachineBinaryNameMachine, h]

theorem step_truncated (output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register), tapesAt source destination base [true] output⟩ =
      some ⟨rejected, clean ambient, tapesAt source destination base [] output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source_inline_MachineBinaryNameMachine]

theorem step_digit (bit : Bool) (rest output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register),
        tapesAt source destination base (true :: bit :: rest) output⟩ =
      some ⟨some again, (ambient, some bit, none),
        tapesAt source destination base rest (bit :: output)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source_inline_MachineBinaryNameMachine, update_destination_inline_MachineBinaryNameMachine]

/-- Total correspondence, including malformed input and its exact unread suffix. -/
theorem scanTrace (input output : List Bool) (last register : Option Bool) :
    (advance (TM2.step program))^[steps input]
      (some ⟨some again, (ambient, last, register),
        tapesAt source destination base input output⟩) =
      some ⟨if (scanSpec input output last).accepted then accepted else rejected,
        clean ambient, tapesAt source destination base
          (scanSpec input output last).remaining (scanSpec input output last).reversedPayload⟩ := by
  induction input using List.twoStepInduction generalizing output last register with
  | nil =>
      simpa only [steps, scanSpec, Bool.false_eq_true, ite_false,
        Function.iterate_one, advance_some] using
        step_empty source destination distinct again accepted rejected program atScan base ambient
          output last register
  | singleton flag =>
      cases flag
      · have h := step_end source destination distinct again accepted rejected program atScan
          base ambient [] output last register
        cases hlast : last.getD true <;>
          simpa [steps, scanSpec, hlast] using h
      · simpa only [steps, scanSpec, Bool.false_eq_true, ite_false,
          Function.iterate_one, advance_some] using
          step_truncated source destination distinct again accepted rejected program atScan base ambient
            output last register
  | cons_cons flag bit rest ih _ =>
      cases flag
      · have h := step_end source destination distinct again accepted rejected program atScan
          base ambient (bit :: rest) output last register
        cases hlast : last.getD true <;>
          simpa [steps, scanSpec, hlast] using h
      · rw [steps, Function.iterate_succ_apply]
        simp only [advance_some]
        rw [step_digit source destination distinct again accepted rejected program atScan]
        exact ih (bit :: output) (some bit) none

/-- A real timed execution; the instruction equation is the only program premise. -/
def scanInTime (input output : List Bool) (last register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (ambient, last, register), tapesAt source destination base input output⟩
      (some ⟨if (scanSpec input output last).accepted then accepted else rejected,
        clean ambient, tapesAt source destination base
          (scanSpec input output last).remaining (scanSpec input output last).reversedPayload⟩)
      (input.length + 1) where
  steps := steps input
  evals_in_steps := scanTrace source destination distinct again accepted rejected program atScan
    base ambient input output last register
  steps_le_m := steps_le input

/-- A complete framed name needs exactly one transition per digit and one for
the terminator. No transition inspects the magnitude denoted by the payload. -/
theorem framedTrace (bits suffix output : List Bool) (register : Option Bool) :
    (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some again, (ambient, none, register),
        tapesAt source destination base (frame bits ++ suffix) output⟩) =
      some ⟨if canonical bits then accepted else rejected, clean ambient,
        tapesAt source destination base suffix (bits.reverse ++ output)⟩ := by
  have h := scanTrace source destination distinct again accepted rejected program atScan
    base ambient (frame bits ++ suffix) output none register
  cases hlast : (finalDigit bits none).getD true <;>
    simpa [steps_frame, scanSpec_frame, canonical, hlast] using h

end Program

/-- One concrete machine with two Boolean stacks and finite control. The two
exit labels expose acceptance to a caller; the scanner leaves them unexecuted. -/
def machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := State Unit
  initialState := clean ()
  m label := if label = 0 then scan false true 0 (some 1) (some 2) else .halt

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

/-- The bounded run instantiated with the displayed finite machine, including
its actual entry and two actual exit labels. -/
def machineInTime (input output : List Bool) :
    StateTransition.EvalsToInTime machine.step
      ⟨some (0 : Fin 3), clean (), tapesAt false true (fun _ : Bool => []) input output⟩
      (some ⟨if (scanSpec input output none).accepted then some (1 : Fin 3) else some (2 : Fin 3),
        clean (), tapesAt false true (fun _ : Bool => [])
          (scanSpec input output none).remaining (scanSpec input output none).reversedPayload⟩)
      (input.length + 1) :=
  scanInTime false true (by decide) (0 : Fin 3) (some 1) (some 2) machine.m
    (by simp [machine]) (fun _ : Bool => []) () input output none none

end MaxCutGames.BinaryNameMachine

end OAI
