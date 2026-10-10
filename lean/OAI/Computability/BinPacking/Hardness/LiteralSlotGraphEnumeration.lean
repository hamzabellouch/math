import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import OAI.Computability.BinPacking.Machines.PackingPowerProgram

namespace OAI

namespace BinPackingGap.LiteralSlotGraphMachine

section

open FiniteTapeProgram BinPackingGames.Foundations.Complexity

def twoTapes (base : Tape → List Bool) (source destination : Tape)
    (input output : List Bool) : Tape → List Bool :=
  Function.update (Function.update base source input) destination output

@[simp] theorem twoTapes_source (base : Tape → List Bool) (source destination : Tape)
    (different : source ≠ destination) (input output : List Bool) :
    twoTapes base source destination input output source = input := by
  simp [twoTapes, different]

@[simp] theorem twoTapes_destination (base : Tape → List Bool) (source destination : Tape)
    (input output : List Bool) :
    twoTapes base source destination input output destination = output := by
  simp [twoTapes]

theorem twoTapes_update_source (base : Tape → List Bool) (source destination : Tape)
    (different : source ≠ destination) (input output next : List Bool) :
    Function.update (twoTapes base source destination input output) source next =
      twoTapes base source destination next output := by
  funext k
  by_cases hs : k = source
  · subst k; simp [twoTapes, different]
  · by_cases hd : k = destination
    · subst k; simp [twoTapes, different.symm]
    · simp [twoTapes, hs, hd]

@[simp] theorem twoTapes_update_destination (base : Tape → List Bool)
    (source destination : Tape) (input output next : List Bool) :
    Function.update (twoTapes base source destination input output) destination next =
      twoTapes base source destination input next := by
  simp [twoTapes]

theorem readVariable_loop_exec (source destination : Tape) (different : source ≠ destination)
    (base : Tape → List Bool) (s : State) (n : Nat) (suffix marks : List Bool) :
    Exec (.loop (.pop source saveHead .done) (fun s => s.2.getD false)
      (.atom (.push destination (fun _ => true) .done)))
      ⟨s, twoTapes base source destination (encodeWord n ++ suffix) marks⟩ (2 * n + 1)
      ⟨(s.1, some false), twoTapes base source destination suffix (List.replicate n true ++ marks)⟩ := by
  induction n generalizing s marks with
  | zero =>
      have h := Exec.loop_false (g := Action.pop source saveHead .done)
        (p := fun s : State => s.2.getD false)
        (a := Code.atom (.push destination (fun _ => true) .done))
        (d := ⟨s, twoTapes base source destination (encodeWord 0 ++ suffix) marks⟩)
        (by simp [Action.eval, saveHead, encodeWord, twoTapes_source, different])
      simpa [Action.eval, saveHead, encodeWord, twoTapes_source, different,
        twoTapes_update_source] using h
  | succ n ih =>
      let d : Data Tape State :=
        ⟨s, twoTapes base source destination (encodeWord (n + 1) ++ suffix) marks⟩
      have body := Exec.atom (.push destination (fun _ => true) .done)
        ((Action.pop source saveHead .done).eval d)
      have bodyEq : (Action.push destination (fun _ : State => true) .done).eval
          ((Action.pop source saveHead .done).eval d) =
          ⟨(s.1, some true), twoTapes base source destination
            (encodeWord n ++ suffix) (true :: marks)⟩ := by
        simp [d, Action.eval, saveHead, encodeWord, List.replicate_succ,
          twoTapes_source, different, twoTapes_update_source]
      rw [bodyEq] at body
      have tail := ih (s.1, some true) (true :: marks)
      have run := Exec.loop_true
        (g := Action.pop source saveHead .done)
        (p := fun s : State => s.2.getD false)
        (by simp [d, Action.eval, saveHead, encodeWord, List.replicate_succ,
          twoTapes_source, different]) body tail
      have marksEq : List.replicate n true ++ true :: marks =
          List.replicate (n + 1) true ++ marks := by
        rw [List.replicate_succ']
        simp only [List.append_assoc, List.singleton_append]
      simpa only [d, marksEq, show 1 + (2 * n + 1) + 1 = 2 * (n + 1) + 1 by omega] using run

theorem readVariable_exec (source destination : Tape) (different : source ≠ destination)
    (base : Tape → List Bool) (s : State) (n : Nat) (suffix marks : List Bool) :
    Exec (readVariable source destination)
      ⟨s, twoTapes base source destination (encodeWord n ++ suffix) marks⟩ (2 * n + 2)
      ⟨(s.1, none), twoTapes base source destination suffix (List.replicate n true ++ marks)⟩ := by
  have run := readVariable_loop_exec source destination different base s n suffix marks
  have final := Exec.atom (.load resetHead .done)
    (Data.mk (s.1, some false) (twoTapes base source destination suffix (List.replicate n true ++ marks)))
  simpa [readVariable, Action.eval, resetHead, Nat.add_assoc] using Exec.seq run final

theorem readSign_exec (source : Tape) (setSign : Control → Bool → Control)
    (base : Tape → List Bool) (s : State) (sign : Bool) (suffix : List Bool) :
    Exec (readSign source setSign)
      ⟨s, Function.update base source (encodeWord (if sign then 1 else 0) ++ suffix)⟩ 1
      ⟨BooleanTapeCode.clean (setSign s.1.1 sign), Function.update base source suffix⟩ := by
  have run := Exec.atom
    (.pop source saveHead
      (.load (fun s => ((setSign s.1.1 (s.2.getD false), ()), s.2))
        (.branch (fun s => s.2.getD false)
          (.pop source saveHead (.load resetHead .done))
          (.load resetHead .done))))
    (Data.mk s (Function.update base source (encodeWord (if sign then 1 else 0) ++ suffix)))
  cases sign <;> simpa [readSign, Action.eval, saveHead, resetHead, BooleanTapeCode.clean,
    encodeWord] using run

abbrev RawLiteral := Nat × Bool

def counterHead (n : Nat) : Option Bool := if n = 0 then none else some true

def comparedControl (a : Control) (left right : Option Bool) : Control :=
  {a with otherHead := left, equal := a.equal && decide (left = right)}

def comparisonResult (a : Control) (n m : Nat) : Control :=
  {a with otherHead := none, equal := a.equal && decide (n = m)}

theorem counter_head_tail_eq (n m : Nat) :
    (decide (counterHead n = counterHead m) && decide (n - 1 = m - 1)) = decide (n = m) := by
  cases n <;> cases m <;> simp [counterHead]

theorem compareGuard_eval (base : Tape → List Bool) (a : Control)
    (register : Option Bool) (n m : Nat) :
    compareGuard.eval
      ⟨((a, ()), register), twoTapes base .comparison .innerVariable
        (List.replicate n true) (List.replicate m true)⟩ =
    ⟨((comparedControl a (counterHead n) (counterHead m), ()), counterHead m),
      twoTapes base .comparison .innerVariable
        (List.replicate (n - 1) true) (List.replicate (m - 1) true)⟩ := by
  cases n <;> cases m <;>
    simp [compareGuard, Action.eval, mapControl, saveHead, comparedControl, counterHead,
      List.replicate_succ, twoTapes_source, twoTapes_update_source,
      show Tape.comparison ≠ Tape.innerVariable by decide]

theorem comparisonResult_step (a : Control) (n m : Nat) :
    comparisonResult (comparedControl a (counterHead n) (counterHead m)) (n - 1) (m - 1) =
      comparisonResult a n m := by
  simp [comparisonResult, comparedControl, Bool.and_assoc, counter_head_tail_eq]

theorem compareLoop_exec (base : Tape → List Bool) (a : Control)
    (register : Option Bool) (n m : Nat) :
    Exec (.loop compareGuard (fun s : State => s.1.1.otherHead.isSome || s.2.isSome) skip)
      ⟨((a, ()), register), twoTapes base .comparison .innerVariable
        (List.replicate n true) (List.replicate m true)⟩
      (2 * max n m + 1)
      ⟨BooleanTapeCode.clean (comparisonResult a n m),
        twoTapes base .comparison .innerVariable [] []⟩ := by
  by_cases hz : n + m = 0
  · have hn : n = 0 := by omega
    have hm : m = 0 := by omega
    subst n; subst m
    have run := Exec.loop_false (g := compareGuard)
      (p := fun s : State => s.1.1.otherHead.isSome || s.2.isSome) (a := skip)
      (d := Data.mk ((a, ()), register) (twoTapes base .comparison .innerVariable [] []))
      (by rw [show ([] : List Bool) = List.replicate 0 true from rfl,
        compareGuard_eval]; simp [comparedControl, counterHead])
    have finish : compareGuard.eval
        ⟨((a, ()), register), twoTapes base .comparison .innerVariable [] []⟩ =
        ⟨BooleanTapeCode.clean (comparisonResult a 0 0),
          twoTapes base .comparison .innerVariable [] []⟩ := by
      simpa [comparisonResult, comparedControl, counterHead, BooleanTapeCode.clean] using
        compareGuard_eval base a register 0 0
    rw [finish] at run
    simpa using run
  · have headNonempty : (counterHead n).isSome || (counterHead m).isSome = true := by
      cases n <;> cases m <;> simp_all [counterHead]
    let next := comparedControl a (counterHead n) (counterHead m)
    let d : Data Tape State :=
      ⟨((a, ()), register), twoTapes base .comparison .innerVariable
        (List.replicate n true) (List.replicate m true)⟩
    have body : Exec skip (compareGuard.eval d) 1 (compareGuard.eval d) :=
      Exec.atom .done _
    have tail := compareLoop_exec base next (counterHead m) (n - 1) (m - 1)
    have run := Exec.loop_true (g := compareGuard)
      (p := fun s : State => s.1.1.otherHead.isSome || s.2.isSome)
      (d := d) (by simpa [d, compareGuard_eval, comparedControl] using headNonempty)
      body (by simpa only [d, compareGuard_eval, next] using tail)
    have cost : 1 + (2 * max (n - 1) (m - 1) + 1) + 1 = 2 * max n m + 1 := by omega
    simpa only [d, next, comparisonResult_step, cost] using run
termination_by n + m
decreasing_by omega

theorem compareVariables_exec (base : Tape → List Bool) (a : Control)
    (register : Option Bool) (n m : Nat) :
    Exec compareVariables
      ⟨((a, ()), register), twoTapes base .comparison .innerVariable
        (List.replicate n true) (List.replicate m true)⟩
      (2 * max n m + 2)
      ⟨BooleanTapeCode.clean {a with otherHead := none, equal := decide (n = m)},
        twoTapes base .comparison .innerVariable [] []⟩ := by
  have first := Exec.atom (.load (mapControl (fun a => {a with equal := true})) .done)
    (Data.mk ((a, ()), register) (twoTapes base .comparison .innerVariable
      (List.replicate n true) (List.replicate m true)))
  have second := compareLoop_exec base {a with equal := true} register n m
  have run := Exec.seq (by simpa [Action.eval, mapControl] using first) second
  simpa [compareVariables, changeControl, comparisonResult,
    show 1 + (2 * max n m + 1) = 2 * max n m + 2 by omega] using run

def vertexBodyCost (i : Nat) : Nat :=
  3 * i.bits.length + UnaryToBinaryMachine.steps 1 i + 6

def vertexRecord (i : Nat) : List Bool := true :: BinaryEncoding.natBits i

theorem vertexBody_exec (base : Tape → List Bool) (a : Control) (register : Option Bool)
    (i : Nat) (hI : base .outerIndex = i.bits) (hU : base .unary = [])
    (hW : base .scratch = []) :
    Exec vertexBody ⟨((a, ()), register), base⟩ (vertexBodyCost i)
      ⟨BooleanTapeCode.clean a,
        Function.update (Function.update base .accumulator
          ((vertexRecord i).reverse ++ base .accumulator)) .outerIndex (i + 1).bits⟩ := by
  let b₁ := Function.update base Tape.accumulator (true :: base .accumulator)
  let b₂ := Function.update b₁ Tape.accumulator
    ((BinPackingCompleteness.BinaryEncoding.frame i.bits).reverse ++ b₁ .accumulator)
  have first : Exec (pushBit .accumulator true) ⟨((a, ()), register), base⟩ 1
      ⟨((a, ()), register), b₁⟩ := Exec.atom _ _
  have emitted := BooleanTapeCode.frame_exec Tape.outerIndex .scratch .accumulator
    (by decide) (by decide) (by decide) b₁ (by simpa [b₁] using hW) a register
  have hi₁ : b₁ .outerIndex = i.bits := by simpa [b₁] using hI
  rw [hi₁] at emitted
  have increased := BooleanTapeCode.increment_exec (n := i) Tape.outerIndex .unary .scratch
    (by decide) (by decide) (by decide) b₂
    (by simpa [b₂, b₁] using hU) (by simpa [b₂, b₁] using hW)
    (by simpa [b₂, b₁] using hI) a none
  have last := Exec.atom (Action.done : Action Tape State)
    (Data.mk (BooleanTapeCode.clean a) (Function.update b₂ .outerIndex (i + 1).bits))
  have run := Exec.seq first (Exec.seq emitted (Exec.seq increased last))
  have bc : 1 + ((3 * i.bits.length + 3) + ((1 + UnaryToBinaryMachine.steps 1 i) + 1)) =
      vertexBodyCost i := by simp [vertexBodyCost]; omega
  simpa [vertexBody, sequence, skip, frame, increment, b₂, b₁, vertexRecord,
    BinaryEncoding.natBits, BinPackingCompleteness.BinaryEncoding.nameBits, bc,
    List.reverse_cons, List.append_assoc, Action.eval] using run

def vertexRecords : Nat → Nat → List Bool
  | _, 0 => []
  | i, n + 1 => vertexRecord i ++ vertexRecords (i + 1) n

def vertexLoopCost : Nat → Nat → Nat
  | 0, _ => 1
  | n + 1, i => vertexBodyCost i + vertexLoopCost n (i + 1) + 1

def vertexResult (base : Tape → List Bool) (n i : Nat) : Tape → List Bool :=
  Function.update (Function.update (Function.update base .vertexCount [])
    .outerIndex (i + n).bits) .accumulator
      ((vertexRecords i n).reverse ++ base .accumulator)

theorem vertices_exec (base : Tape → List Bool) (a : Control) (register : Option Bool)
    (n i : Nat) (hN : base .vertexCount = List.replicate n true)
    (hI : base .outerIndex = i.bits) (hU : base .unary = []) (hW : base .scratch = []) :
    Exec vertices ⟨((a, ()), register), base⟩ (vertexLoopCost n i)
      ⟨BooleanTapeCode.clean a, vertexResult base n i⟩ := by
  induction n generalizing base i register with
  | zero =>
      have run := Exec.loop_false (g := Action.pop Tape.vertexCount saveHead .done)
        (p := fun s : State => s.2.isSome) (a := vertexBody)
        (d := Data.mk ((a, ()), register) base)
        (by simp [Action.eval, saveHead, hN])
      have result : vertexResult base 0 i = Function.update base Tape.vertexCount [] := by
        funext tape
        cases tape <;> simp [vertexResult, vertexRecords, hI]
      simpa [vertices, vertexLoopCost, Action.eval, saveHead, hN,
        BooleanTapeCode.clean, result] using run
  | succ n ih =>
      let b₀ := Function.update base Tape.vertexCount (List.replicate n true)
      let b₁ := Function.update (Function.update b₀ Tape.accumulator
        ((vertexRecord i).reverse ++ b₀ .accumulator)) Tape.outerIndex (i + 1).bits
      have guardEq : (Action.pop Tape.vertexCount saveHead .done).eval
          ⟨((a, ()), register), base⟩ = ⟨((a, ()), some true), b₀⟩ := by
        simp [Action.eval, saveHead, hN, List.replicate_succ, b₀]
      have body := vertexBody_exec b₀ a (some true) i
        (by simpa [b₀] using hI) (by simpa [b₀] using hU) (by simpa [b₀] using hW)
      have tail := ih b₁ none (i + 1)
        (by simp [b₁, b₀]) (by simp [b₁])
        (by simpa [b₁, b₀] using hU) (by simpa [b₁, b₀] using hW)
      have run := Exec.loop_true (g := Action.pop Tape.vertexCount saveHead .done)
        (p := fun s : State => s.2.isSome)
        (d := Data.mk ((a, ()), register) base)
        (by rw [guardEq]; rfl)
        (by simpa only [guardEq, BooleanTapeCode.clean, b₁] using body) tail
      have result : vertexResult b₁ n (i + 1) = vertexResult base (n + 1) i := by
        funext tape
        cases tape <;> simp [vertexResult, vertexRecords, b₁, b₀,
          List.reverse_append, List.append_assoc, Nat.add_comm, Nat.add_left_comm]
      simpa only [vertices, vertexLoopCost, result] using run

theorem bits_length_le (n : Nat) : n.bits.length ≤ n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr n.lt_two_pow_self

theorem vertexBodyCost_le (i : Nat) : vertexBodyCost i ≤ 5 * i + 12 := by
  have hs := UnaryToBinaryMachine.steps_le 1 i
  have hb := bits_length_le i
  simp only [vertexBodyCost]
  nlinarith

theorem vertexLoopCost_le (n i : Nat) :
    vertexLoopCost n i ≤ n * (5 * (i + n) + 13) + 1 := by
  induction n generalizing i with
  | zero => simp [vertexLoopCost]
  | succ n ih =>
      have hs := vertexBodyCost_le i
      have ht := ih (i + 1)
      simp only [vertexLoopCost]
      nlinarith

theorem vertexRecords_range (i n : Nat) :
    vertexRecords i n = (List.range' i n).flatMap vertexRecord := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [vertexRecords, List.range'_succ, ih]

theorem vertexRecords_listBits (i n : Nat) :
    vertexRecords i n ++ [false] =
      BinaryEncoding.listBits BinaryEncoding.natBits (List.range' i n) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      simp [vertexRecords, List.range'_succ, vertexRecord, BinaryEncoding.listBits,
        List.append_assoc, ih]

def pairRecord (u v : Nat) : List Bool :=
  true :: (BinaryEncoding.natBits u ++ BinaryEncoding.natBits v)

def pairCost (u v : Nat) : Nat := 3 * u.bits.length + 3 * v.bits.length + 8

theorem emitPair_exec (base : Tape → List Bool) (a : Control) (register : Option Bool)
    (u v : Nat) (hU : base .outerIndex = u.bits) (hV : base .innerIndex = v.bits)
    (hW : base .scratch = []) :
    Exec emitPair ⟨((a, ()), register), base⟩ (pairCost u v)
      ⟨BooleanTapeCode.clean a, Function.update base .accumulator
        ((pairRecord u v).reverse ++ base .accumulator)⟩ := by
  let b₁ := Function.update base Tape.accumulator (true :: base .accumulator)
  let b₂ := Function.update b₁ Tape.accumulator
    ((BinPackingCompleteness.BinaryEncoding.frame u.bits).reverse ++ b₁ .accumulator)
  let b₃ := Function.update b₂ Tape.accumulator
    ((BinPackingCompleteness.BinaryEncoding.frame v.bits).reverse ++ b₂ .accumulator)
  have first : Exec (pushBit .accumulator true) ⟨((a, ()), register), base⟩ 1
      ⟨((a, ()), register), b₁⟩ := Exec.atom _ _
  have left := BooleanTapeCode.frame_exec Tape.outerIndex .scratch .accumulator
    (by decide) (by decide) (by decide) b₁ (by simpa [b₁] using hW) a register
  have hi₁ : b₁ .outerIndex = u.bits := by simpa [b₁] using hU
  rw [hi₁] at left
  have right := BooleanTapeCode.frame_exec Tape.innerIndex .scratch .accumulator
    (by decide) (by decide) (by decide) b₂ (by simpa [b₂, b₁] using hW) a none
  have hi₂ : b₂ .innerIndex = v.bits := by simpa [b₂, b₁] using hV
  rw [hi₂] at right
  have last : Exec skip ⟨BooleanTapeCode.clean a, b₃⟩ 1
      ⟨BooleanTapeCode.clean a, b₃⟩ := Exec.atom .done _
  have run := Exec.seq first (Exec.seq left (Exec.seq right last))
  have cost : 1 + ((3 * u.bits.length + 3) + ((3 * v.bits.length + 3) + 1)) = pairCost u v := by
    simp [pairCost]; omega
  simpa [emitPair, sequence, frame, b₃, b₂, b₁, pairRecord, BinaryEncoding.natBits,
    BinPackingCompleteness.BinaryEncoding.nameBits, cost, List.reverse_cons,
    List.reverse_append, List.append_assoc] using run

def literalBits (literal : RawLiteral) : List Bool :=
  encodeWord literal.1 ++ encodeWord (if literal.2 then 1 else 0)

def literalsBits (literals : List RawLiteral) : List Bool := literals.flatMap literalBits

def bodyEdge (a : Control) (left right : RawLiteral) : Prop :=
  0 < a.remaining.val ∨ (left.1 = right.1 ∧ a.outerSign ≠ right.2)

instance (a : Control) (left right : RawLiteral) : Decidable (bodyEdge a left right) := by
  unfold bodyEdge
  infer_instance

def bodyControl (a : Control) (left right : RawLiteral) : Control :=
  nextRemaining {a with innerSign := right.2, otherHead := none, equal := decide (left.1 = right.1)}

def branchCost (a : Control) (left right : RawLiteral) (u v : Nat) : Nat :=
  if bodyEdge a left right then pairCost u v + 1 else 2

def innerBodyCost (a : Control) (left right : RawLiteral) (u v : Nat) : Nat :=
  (2 * right.1 + 2) + (1 + (2 * (left.1 + 1) + ((2 * max left.1 right.1 + 2) +
    (branchCost a left right u v + ((1 + UnaryToBinaryMachine.steps 1 v) + (1 + 1))))))

def bodyAccumulator (base : Tape → List Bool) (a : Control) (left right : RawLiteral)
    (u v : Nat) : List Bool :=
  if bodyEdge a left right then (pairRecord u v).reverse ++ base .accumulator
  else base .accumulator

def innerBodyResult (base : Tape → List Bool) (a : Control) (left right : RawLiteral)
    (u v : Nat) (suffix : List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update base .innerSource suffix)
    .accumulator (bodyAccumulator base a left right u v)) .innerIndex (v + 1).bits

theorem innerBody_exec (base : Tape → List Bool) (a : Control) (register : Option Bool)
    (left right : RawLiteral) (u v : Nat) (suffix : List Bool)
    (hS : base .innerSource = literalBits right ++ suffix)
    (hL : base .outerVariable = List.replicate left.1 true)
    (hR : base .innerVariable = []) (hC : base .comparison = [])
    (hU : base .outerIndex = u.bits) (hV : base .innerIndex = v.bits)
    (hW : base .scratch = []) (hN : base .unary = []) :
    Exec innerBody ⟨((a, ()), register), base⟩ (innerBodyCost a left right u v)
      ⟨BooleanTapeCode.clean (bodyControl a left right),
        innerBodyResult base a left right u v suffix⟩ := by
  let signBits := encodeWord (if right.2 then 1 else 0)
  let b₁ := twoTapes base Tape.innerSource Tape.innerVariable
    (signBits ++ suffix) (List.replicate right.1 true)
  let a₁ := {a with innerSign := right.2}
  let b₂ := Function.update b₁ Tape.innerSource suffix
  let b₃ := Function.update b₂ Tape.comparison (List.replicate left.1 true)
  let a₂ := {a₁ with otherHead := none, equal := decide (left.1 = right.1)}
  let b₄ := twoTapes b₃ Tape.comparison Tape.innerVariable [] []
  let b₅ := Function.update b₄ Tape.accumulator (bodyAccumulator base a left right u v)
  let b₆ := Function.update b₅ Tape.innerIndex (v + 1).bits
  have first := readVariable_exec Tape.innerSource .innerVariable (by decide)
    base ((a, ()), register) right.1 (signBits ++ suffix) []
  have startEq : twoTapes base Tape.innerSource Tape.innerVariable
      (encodeWord right.1 ++ (signBits ++ suffix)) [] = base := by
    funext tape
    cases tape <;> simp [twoTapes, hS, hR, literalBits, signBits, List.append_assoc]
  rw [startEq] at first
  simp only [List.append_nil] at first
  have signed := readSign_exec Tape.innerSource (fun a b => {a with innerSign := b}) b₁
    (BooleanTapeCode.clean a) right.2 suffix
  have signStart : Function.update b₁ Tape.innerSource (signBits ++ suffix) = b₁ := by
    simp [b₁, twoTapes]
  change Exec (readSign .innerSource (fun a b => {a with innerSign := b}))
    ⟨BooleanTapeCode.clean a, Function.update b₁ .innerSource (signBits ++ suffix)⟩ 1
    ⟨BooleanTapeCode.clean a₁, b₂⟩ at signed
  rw [signStart] at signed
  have copied := BooleanTapeCode.copy_exec Tape.outerVariable .comparison .scratch
    (by decide) (by decide) (by decide) b₂ (by simpa [b₂, b₁, twoTapes] using hW)
    (BooleanTapeCode.clean a₁)
  have outerWord : b₂ .outerVariable = List.replicate left.1 true := by
    simpa [b₂, b₁, twoTapes] using hL
  have compEmpty : b₂ .comparison = [] := by simpa [b₂, b₁, twoTapes] using hC
  rw [outerWord, compEmpty, List.append_nil, List.length_replicate] at copied
  have compared := compareVariables_exec b₃ a₁ none left.1 right.1
  have compareStart : twoTapes b₃ Tape.comparison Tape.innerVariable
      (List.replicate left.1 true) (List.replicate right.1 true) = b₃ := by
    funext tape
    cases tape <;> simp [b₃, b₂, b₁, twoTapes]
  rw [compareStart] at compared
  have chosen : Exec (.branch isEdge emitPair skip) ⟨BooleanTapeCode.clean a₂, b₄⟩
      (branchCost a left right u v) ⟨BooleanTapeCode.clean a₂, b₅⟩ := by
    have testEq : isEdge (BooleanTapeCode.clean a₂) = decide (bodyEdge a left right) := by
      cases hs : a.outerSign <;> cases hr : right.2 <;>
        simp [isEdge, BooleanTapeCode.clean, a₂, a₁, bodyEdge, hs, hr]
    by_cases edge : bodyEdge a left right
    · have emitted := emitPair_exec b₄ a₂ none u v
        (by simpa [b₄, b₃, b₂, b₁, twoTapes] using hU)
        (by simpa [b₄, b₃, b₂, b₁, twoTapes] using hV)
        (by simpa [b₄, b₃, b₂, b₁, twoTapes] using hW)
      have run := Exec.branch_true (p := isEdge) (b := skip)
        (by change isEdge (BooleanTapeCode.clean a₂) = true; simp [testEq, edge]) emitted
      simpa [b₅, bodyAccumulator, branchCost, edge, b₄, b₃, b₂, b₁, twoTapes,
        BooleanTapeCode.clean] using run
    · have unchanged : b₅ = b₄ := by
        funext tape
        cases tape <;> simp [b₅, bodyAccumulator, edge, b₄, b₃, b₂, b₁, twoTapes]
      have run := Exec.branch_false (p := isEdge) (a := emitPair)
        (by change isEdge (BooleanTapeCode.clean a₂) = false; simp [testEq, edge])
        (Exec.atom (Action.done : Action Tape State) (Data.mk (BooleanTapeCode.clean a₂) b₄))
      simpa [branchCost, edge, unchanged, skip, Action.eval] using run
  have increased := BooleanTapeCode.increment_exec (n := v) Tape.innerIndex .unary .scratch
    (by decide) (by decide) (by decide) b₅
    (by simpa [b₅, b₄, b₃, b₂, b₁, twoTapes] using hN)
    (by simpa [b₅, b₄, b₃, b₂, b₁, twoTapes] using hW)
    (by simpa [b₅, b₄, b₃, b₂, b₁, twoTapes] using hV) a₂ none
  have changed : Exec (changeControl nextRemaining) ⟨BooleanTapeCode.clean a₂, b₆⟩ 1
      ⟨BooleanTapeCode.clean (nextRemaining a₂), b₆⟩ := Exec.atom _ _
  have last : Exec skip ⟨BooleanTapeCode.clean (nextRemaining a₂), b₆⟩ 1
      ⟨BooleanTapeCode.clean (nextRemaining a₂), b₆⟩ := Exec.atom .done _
  have run := Exec.seq first (Exec.seq signed (Exec.seq copied (Exec.seq compared
    (Exec.seq chosen (Exec.seq increased (Exec.seq changed last))))))
  have endEq : b₆ = innerBodyResult base a left right u v suffix := by
    funext tape
    cases tape <;> simp [b₆, b₅, b₄, b₃, b₂, b₁, twoTapes, innerBodyResult, hC, hR]
  simpa only [innerBody, sequence, copy, increment, skip, innerBodyCost,
    bodyControl, a₂, a₁, endEq] using run

theorem pairCost_le (u v : Nat) : pairCost u v ≤ 3 * u + 3 * v + 8 := by
  have hu := bits_length_le u
  have hv := bits_length_le v
  simp only [pairCost]
  omega

theorem innerBodyCost_le (a : Control) (left right : RawLiteral) (u v B : Nat)
    (hL : left.1 ≤ B) (hR : right.1 ≤ B) (hU : u ≤ B) (hV : v ≤ B) :
    innerBodyCost a left right u v ≤ 14 * B + 25 := by
  have hp := pairCost_le u v
  have hi := UnaryToBinaryMachine.steps_le 1 v
  have hb : branchCost a left right u v ≤ 3 * u + 3 * v + 9 := by
    unfold branchCost
    split_ifs <;> omega
  have hm : max left.1 right.1 ≤ B := max_le hL hR
  simp only [innerBodyCost]
  omega

def rowEdges (u v : Nat) (left : RawLiteral) : List RawLiteral → List (Nat × Nat)
  | [] => []
  | right :: rest =>
      let tail := rowEdges u (v + 1) left rest
      if u / 3 = v / 3 ∨ (left.1 = right.1 ∧ left.2 ≠ right.2)
      then (u, v) :: tail else tail

def suffixEdges (u : Nat) : List RawLiteral → List (Nat × Nat)
  | [] => []
  | literal :: rest => rowEdges u (u + 1) literal rest ++ suffixEdges (u + 1) rest

theorem literalsBits_cons (literal : RawLiteral) (rest : List RawLiteral) :
    literalsBits (literal :: rest) = literalBits literal ++ literalsBits rest := rfl

theorem literalsBits_ne_nil (literals : List RawLiteral) :
    literalsBits literals = [] ↔ literals = [] := by
  cases literals with
  | nil => simp [literalsBits]
  | cons literal rest => simp [literalsBits, literalBits, encodeWord]

theorem remaining_same_clause (u t : Nat) :
    0 < (2 - u % 3) - t ↔ u / 3 = (u + 1 + t) / 3 := by
  omega

def edgeRecords (edges : List (Nat × Nat)) : List Bool :=
  edges.flatMap (fun edge => pairRecord edge.1 edge.2)

def rowControl (a : Control) (left : RawLiteral) : List RawLiteral → Control
  | [] => a
  | right :: rest => rowControl (bodyControl a left right) left rest

def innerLoopCost (a : Control) (left : RawLiteral) (u v : Nat) : List RawLiteral → Nat
  | [] => 1
  | right :: rest => innerBodyCost a left right u v +
      innerLoopCost (bodyControl a left right) left u (v + 1) rest + 1

def innerLoopResult (base : Tape → List Bool) (left : RawLiteral) (u v : Nat)
    (rest : List RawLiteral) : Tape → List Bool :=
  Function.update (Function.update (Function.update base .innerSource [])
    .innerIndex (v + rest.length).bits) .accumulator
      ((edgeRecords (rowEdges u v left rest)).reverse ++ base .accumulator)

theorem bodyControl_remaining (a : Control) (left right : RawLiteral) :
    (bodyControl a left right).remaining.val = a.remaining.val - 1 := rfl

@[simp] theorem bodyControl_slot (a : Control) (left right : RawLiteral) :
    (bodyControl a left right).slot = a.slot := rfl

@[simp] theorem bodyControl_outerSign (a : Control) (left right : RawLiteral) :
    (bodyControl a left right).outerSign = a.outerSign := rfl

@[simp] theorem rowControl_slot (a : Control) (left : RawLiteral) (rest : List RawLiteral) :
    (rowControl a left rest).slot = a.slot := by
  induction rest generalizing a with
  | nil => rfl
  | cons right rest ih => simp [rowControl, ih]

@[simp] theorem rowControl_outerSign (a : Control) (left : RawLiteral) (rest : List RawLiteral) :
    (rowControl a left rest).outerSign = a.outerSign := by
  induction rest generalizing a with
  | nil => rfl
  | cons right rest ih => simp [rowControl, ih]

theorem innerLoop_exec (base : Tape → List Bool) (a : Control) (register : Option Bool)
    (left : RawLiteral) (u t : Nat) (rest : List RawLiteral)
    (hS : base .innerSource = literalsBits rest)
    (hL : base .outerVariable = List.replicate left.1 true)
    (hR : base .innerVariable = []) (hC : base .comparison = [])
    (hU : base .outerIndex = u.bits) (hV : base .innerIndex = (u + 1 + t).bits)
    (hW : base .scratch = []) (hN : base .unary = [])
    (hA : a.outerSign = left.2) (hT : a.remaining.val = (2 - u % 3) - t) :
    Exec innerLoop ⟨((a, ()), register), base⟩
      (innerLoopCost a left u (u + 1 + t) rest)
      ⟨BooleanTapeCode.clean (rowControl a left rest),
        innerLoopResult base left u (u + 1 + t) rest⟩ := by
  induction rest generalizing base a register t with
  | nil =>
      have run := Exec.loop_false (g := Action.peek Tape.innerSource saveHead .done)
        (p := fun s : State => s.2.isSome) (a := innerBody)
        (d := Data.mk ((a, ()), register) base)
        (by simp [Action.eval, saveHead, hS, literalsBits])
      have result : innerLoopResult base left u (u + 1 + t) [] = base := by
        funext tape
        cases tape <;> simp [innerLoopResult, rowEdges, edgeRecords, hS, literalsBits, hV]
      simpa [innerLoop, innerLoopCost, rowControl, Action.eval, saveHead, hS,
        literalsBits, BooleanTapeCode.clean, result] using run
  | cons right rest ih =>
      let v := u + 1 + t
      let a₁ := bodyControl a left right
      let b₁ := innerBodyResult base a left right u v (literalsBits rest)
      have guardEq : (Action.peek Tape.innerSource saveHead .done).eval
          ⟨((a, ()), register), base⟩ = ⟨((a, ()), (base .innerSource).head?), base⟩ := rfl
      have sourceNonempty : (base .innerSource).head?.isSome = true := by
        rw [hS]
        cases hv : right.1 <;>
          simp [literalsBits, literalBits, encodeWord, hv, List.replicate_succ]
      have body := innerBody_exec base a (base .innerSource).head? left right u v
        (literalsBits rest) (by simpa only [literalsBits_cons] using hS)
        hL hR hC hU hV hW hN
      have indexEq : v + 1 = u + 1 + (t + 1) := by dsimp [v]; omega
      have tail := ih b₁ a₁ none (t + 1)
        (by simp [b₁, innerBodyResult])
        (by simpa [b₁, innerBodyResult] using hL)
        (by simpa [b₁, innerBodyResult] using hR)
        (by simpa [b₁, innerBodyResult] using hC)
        (by simpa [b₁, innerBodyResult] using hU)
        (by simp [b₁, innerBodyResult, indexEq])
        (by simpa [b₁, innerBodyResult] using hW)
        (by simpa [b₁, innerBodyResult] using hN)
        (by simpa [a₁] using hA)
        (by simp only [a₁, bodyControl_remaining, hT]; omega)
      rw [← indexEq] at tail
      have run := Exec.loop_true (g := Action.peek Tape.innerSource saveHead .done)
        (p := fun s : State => s.2.isSome)
        (d := Data.mk ((a, ()), register) base)
        (by simpa only [guardEq] using sourceNonempty)
        (by simpa only [guardEq, BooleanTapeCode.clean, a₁, b₁] using body) tail
      have edgeIff : bodyEdge a left right ↔
          u / 3 = v / 3 ∨ (left.1 = right.1 ∧ left.2 ≠ right.2) := by
        simp only [bodyEdge, hT, hA, remaining_same_clause, v]
      have result : innerLoopResult b₁ left u (v + 1) rest =
          innerLoopResult base left u v (right :: rest) := by
        funext tape
        by_cases edge : bodyEdge a left right
        · have selected := edgeIff.mp edge
          cases tape <;>
            simp [innerLoopResult, b₁, innerBodyResult, rowEdges, edgeRecords,
              bodyAccumulator, edge, selected, List.reverse_append, List.append_assoc,
              Nat.add_assoc, Nat.add_comm]
        · have omitted : ¬(u / 3 = v / 3 ∨ (left.1 = right.1 ∧ left.2 ≠ right.2)) :=
            fun h => edge (edgeIff.mpr h)
          cases tape <;>
            simp [innerLoopResult, b₁, innerBodyResult, rowEdges, edgeRecords,
              bodyAccumulator, edge, omitted, Nat.add_assoc, Nat.add_comm]
      simpa only [innerLoop, innerLoopCost, rowControl, a₁, v, result] using run

theorem innerLoopCost_le (a : Control) (left : RawLiteral) (u v B : Nat)
    (rest : List RawLiteral) (hL : left.1 ≤ B) (hU : u ≤ B)
    (hV : v + rest.length ≤ B) (hR : ∀ right ∈ rest, right.1 ≤ B) :
    innerLoopCost a left u v rest ≤ rest.length * (14 * B + 26) + 1 := by
  induction rest generalizing a v with
  | nil => simp [innerLoopCost]
  | cons right rest ih =>
      have hb := innerBodyCost_le a left right u v B hL (hR right (by simp)) hU (by simp_all; omega)
      have ht := ih (bodyControl a left right) (v + 1) (by simp_all; omega)
        (fun x hx => hR x (by simp [hx]))
      simp only [innerLoopCost, List.length_cons]
      nlinarith

def rowStartControl (a : Control) (left : RawLiteral) : Control :=
  startRow {a with outerSign := left.2}

def outerBodyControl (a : Control) (left : RawLiteral) (rest : List RawLiteral) : Control :=
  nextSlot (rowControl (rowStartControl a left) left rest)

def outerBodyCost (a : Control) (left : RawLiteral) (u : Nat) (rest : List RawLiteral) : Nat :=
  (2 * left.1 + 2) + (1 + (2 * ((literalsBits rest).length + 1) +
    (2 * (u.bits.length + 1) + ((1 + UnaryToBinaryMachine.steps 1 u) + (1 +
      (innerLoopCost (rowStartControl a left) left u (u + 1) rest +
        (((u + 1 + rest.length).bits.length + 1) + ((left.1 + 1) +
          ((1 + UnaryToBinaryMachine.steps 1 u) + (1 + 1))))))))))

def outerBodyResult (base : Tape → List Bool) (left : RawLiteral) (u : Nat)
    (rest : List RawLiteral) : Tape → List Bool :=
  Function.update (Function.update (Function.update base .input (literalsBits rest))
    .accumulator ((edgeRecords (rowEdges u (u + 1) left rest)).reverse ++ base .accumulator))
      .outerIndex (u + 1).bits

theorem outerBody_exec (base : Tape → List Bool) (a : Control) (register : Option Bool)
    (left : RawLiteral) (u : Nat) (rest : List RawLiteral)
    (hS : base .input = literalBits left ++ literalsBits rest)
    (hL : base .outerVariable = []) (hR : base .innerVariable = [])
    (hC : base .comparison = []) (hU : base .outerIndex = u.bits)
    (hV : base .innerIndex = []) (hI : base .innerSource = [])
    (hW : base .scratch = []) (hN : base .unary = []) (hA : a.slot.val = u % 3) :
    Exec outerBody ⟨((a, ()), register), base⟩ (outerBodyCost a left u rest)
      ⟨BooleanTapeCode.clean (outerBodyControl a left rest), outerBodyResult base left u rest⟩ := by
  let signBits := encodeWord (if left.2 then 1 else 0)
  let b₁ := twoTapes base Tape.input Tape.outerVariable
    (signBits ++ literalsBits rest) (List.replicate left.1 true)
  let a₁ := {a with outerSign := left.2}
  let b₂ := Function.update b₁ Tape.input (literalsBits rest)
  let b₃ := Function.update b₂ Tape.innerSource (literalsBits rest)
  let b₄ := Function.update b₃ Tape.innerIndex u.bits
  let b₅ := Function.update b₄ Tape.innerIndex (u + 1).bits
  let a₂ := rowStartControl a left
  let ar := rowControl a₂ left rest
  let b₆ := innerLoopResult b₅ left u (u + 1) rest
  let b₇ := Function.update b₆ Tape.innerIndex []
  let b₈ := Function.update b₇ Tape.outerVariable []
  let b₉ := Function.update b₈ Tape.outerIndex (u + 1).bits
  have first := readVariable_exec Tape.input .outerVariable (by decide) base
    ((a, ()), register) left.1 (signBits ++ literalsBits rest) []
  have startEq : twoTapes base Tape.input Tape.outerVariable
      (encodeWord left.1 ++ (signBits ++ literalsBits rest)) [] = base := by
    funext tape
    cases tape <;> simp [twoTapes, hS, hL, literalBits, signBits, List.append_assoc]
  rw [startEq] at first
  simp only [List.append_nil] at first
  have signed := readSign_exec Tape.input (fun a b => {a with outerSign := b}) b₁
    (BooleanTapeCode.clean a) left.2 (literalsBits rest)
  have signStart : Function.update b₁ Tape.input (signBits ++ literalsBits rest) = b₁ := by
    simp [b₁, twoTapes]
  change Exec (readSign .input (fun a b => {a with outerSign := b}))
    ⟨BooleanTapeCode.clean a, Function.update b₁ .input (signBits ++ literalsBits rest)⟩ 1
    ⟨BooleanTapeCode.clean a₁, b₂⟩ at signed
  rw [signStart] at signed
  have sourceCopy := BooleanTapeCode.copy_exec Tape.input .innerSource .scratch
    (by decide) (by decide) (by decide) b₂ (by simpa [b₂, b₁, twoTapes] using hW)
    (BooleanTapeCode.clean a₁)
  have inputWord : b₂ .input = literalsBits rest := by simp [b₂]
  have sourceEmpty : b₂ .innerSource = [] := by simpa [b₂, b₁, twoTapes] using hI
  rw [inputWord, sourceEmpty, List.append_nil] at sourceCopy
  have indexCopy := BooleanTapeCode.copy_exec Tape.outerIndex .innerIndex .scratch
    (by decide) (by decide) (by decide) b₃ (by simpa [b₃, b₂, b₁, twoTapes] using hW)
    (BooleanTapeCode.clean a₁)
  have indexWord : b₃ .outerIndex = u.bits := by simpa [b₃, b₂, b₁, twoTapes] using hU
  have indexEmpty : b₃ .innerIndex = [] := by simpa [b₃, b₂, b₁, twoTapes] using hV
  rw [indexWord, indexEmpty, List.append_nil] at indexCopy
  have increased := BooleanTapeCode.increment_exec (n := u) Tape.innerIndex .unary .scratch
    (by decide) (by decide) (by decide) b₄
    (by simpa [b₄, b₃, b₂, b₁, twoTapes] using hN)
    (by simpa [b₄, b₃, b₂, b₁, twoTapes] using hW) (by simp [b₄]) a₁ none
  have started : Exec (changeControl startRow) ⟨BooleanTapeCode.clean a₁, b₅⟩ 1
      ⟨BooleanTapeCode.clean a₂, b₅⟩ := Exec.atom _ _
  have row := innerLoop_exec b₅ a₂ none left u 0 rest
    (by simp [b₅, b₄, b₃]) (by simp [b₅, b₄, b₃, b₂, b₁, twoTapes])
    (by simpa [b₅, b₄, b₃, b₂, b₁, twoTapes] using hR)
    (by simpa [b₅, b₄, b₃, b₂, b₁, twoTapes] using hC)
    (by simpa [b₅, b₄, b₃, b₂, b₁, twoTapes] using hU)
    (by simp [b₅])
    (by simpa [b₅, b₄, b₃, b₂, b₁, twoTapes] using hW)
    (by simpa [b₅, b₄, b₃, b₂, b₁, twoTapes] using hN)
    rfl (by simp [a₂, rowStartControl, startRow, hA])
  simp only [Nat.add_zero] at row
  have clearIndex := BooleanTapeCode.drain_exec Tape.innerIndex b₆ (BooleanTapeCode.clean ar)
  have finalIndex : b₆ .innerIndex = (u + 1 + rest.length).bits := by simp [b₆, innerLoopResult]
  rw [finalIndex] at clearIndex
  have clearVariable := BooleanTapeCode.drain_exec Tape.outerVariable b₇ (BooleanTapeCode.clean ar)
  have variableWord : b₇ .outerVariable = List.replicate left.1 true := by
    simp [b₇, b₆, innerLoopResult, b₅, b₄, b₃, b₂, b₁, twoTapes]
  rw [variableWord, List.length_replicate] at clearVariable
  have advanceOuter := BooleanTapeCode.increment_exec (n := u) Tape.outerIndex .unary .scratch
    (by decide) (by decide) (by decide) b₈
    (by simpa [b₈, b₇, b₆, innerLoopResult, b₅, b₄, b₃, b₂, b₁, twoTapes] using hN)
    (by simpa [b₈, b₇, b₆, innerLoopResult, b₅, b₄, b₃, b₂, b₁, twoTapes] using hW)
    (by simpa [b₈, b₇, b₆, innerLoopResult, b₅, b₄, b₃, b₂, b₁, twoTapes] using hU) ar none
  have advanceSlot : Exec (changeControl nextSlot) ⟨BooleanTapeCode.clean ar, b₉⟩ 1
      ⟨BooleanTapeCode.clean (nextSlot ar), b₉⟩ := Exec.atom _ _
  have last : Exec skip ⟨BooleanTapeCode.clean (nextSlot ar), b₉⟩ 1
      ⟨BooleanTapeCode.clean (nextSlot ar), b₉⟩ := Exec.atom .done _
  have run := Exec.seq first (Exec.seq signed (Exec.seq sourceCopy (Exec.seq indexCopy
    (Exec.seq increased (Exec.seq started (Exec.seq row (Exec.seq clearIndex
      (Exec.seq clearVariable (Exec.seq advanceOuter (Exec.seq advanceSlot last))))))))))
  have endEq : b₉ = outerBodyResult base left u rest := by
    funext tape
    cases tape <;>
      simp [b₉, b₈, b₇, b₆, innerLoopResult, b₅, b₄, b₃, b₂, b₁, twoTapes,
        outerBodyResult, hL, hI, hV]
  simpa only [outerBody, sequence, copy, increment, drain, skip, outerBodyCost,
    outerBodyControl, a₂, ar, endEq] using run

theorem outerBodyControl_slot (a : Control) (left : RawLiteral) (rest : List RawLiteral) :
    (outerBodyControl a left rest).slot.val = (a.slot.val + 1) % 3 := by
  simp [outerBodyControl, nextSlot, rowStartControl, startRow]

theorem outerBodyCost_le (a : Control) (left : RawLiteral) (u B : Nat) (rest : List RawLiteral)
    (hL : left.1 ≤ B) (hU : u + 1 + rest.length ≤ B)
    (hS : (literalsBits rest).length ≤ B) (hR : ∀ right ∈ rest, right.1 ≤ B) :
    outerBodyCost a left u rest ≤ 40 * (B + 1) ^ 2 := by
  have hu : u ≤ B := by omega
  have hcount : rest.length ≤ B := by omega
  have huBits := bits_length_le u
  have hvBits := bits_length_le (u + 1 + rest.length)
  have inc := UnaryToBinaryMachine.steps_le 1 u
  have row := innerLoopCost_le (rowStartControl a left) left u (u + 1) B rest hL hu hU hR
  have rowBound := Nat.mul_le_mul_right (14 * B + 26) hcount
  simp only [outerBodyCost]
  nlinarith

def outerControl (a : Control) : List RawLiteral → Control
  | [] => a
  | left :: rest => outerControl (outerBodyControl a left rest) rest

def outerLoopCost (a : Control) (u : Nat) : List RawLiteral → Nat
  | [] => 1
  | left :: rest => outerBodyCost a left u rest +
      outerLoopCost (outerBodyControl a left rest) (u + 1) rest + 1

def outerLoopResult (base : Tape → List Bool) (u : Nat) (literals : List RawLiteral) : Tape → List Bool :=
  Function.update (Function.update (Function.update base .input [])
    .outerIndex (u + literals.length).bits) .accumulator
      ((edgeRecords (suffixEdges u literals)).reverse ++ base .accumulator)

theorem outerLoop_exec (base : Tape → List Bool) (a : Control) (register : Option Bool)
    (u : Nat) (literals : List RawLiteral) (hS : base .input = literalsBits literals)
    (hL : base .outerVariable = []) (hR : base .innerVariable = [])
    (hC : base .comparison = []) (hU : base .outerIndex = u.bits)
    (hV : base .innerIndex = []) (hI : base .innerSource = [])
    (hW : base .scratch = []) (hN : base .unary = []) (hA : a.slot.val = u % 3) :
    Exec outerLoop ⟨((a, ()), register), base⟩ (outerLoopCost a u literals)
      ⟨BooleanTapeCode.clean (outerControl a literals), outerLoopResult base u literals⟩ := by
  induction literals generalizing base a register u with
  | nil =>
      have run := Exec.loop_false (g := Action.peek Tape.input saveHead .done)
        (p := fun s : State => s.2.isSome) (a := outerBody)
        (d := Data.mk ((a, ()), register) base)
        (by simp [Action.eval, saveHead, hS, literalsBits])
      have result : outerLoopResult base u [] = base := by
        funext tape
        cases tape <;> simp [outerLoopResult, suffixEdges, edgeRecords, hS, literalsBits, hU]
      simpa [outerLoop, outerLoopCost, outerControl, Action.eval, saveHead, hS,
        literalsBits, BooleanTapeCode.clean, result] using run
  | cons left rest ih =>
      let a₁ := outerBodyControl a left rest
      let b₁ := outerBodyResult base left u rest
      have guardEq : (Action.peek Tape.input saveHead .done).eval
          ⟨((a, ()), register), base⟩ = ⟨((a, ()), (base .input).head?), base⟩ := rfl
      have sourceNonempty : (base .input).head?.isSome = true := by
        rw [hS]
        cases hv : left.1 <;>
          simp [literalsBits, literalBits, encodeWord, hv, List.replicate_succ]
      have body := outerBody_exec base a (base .input).head? left u rest
        (by simpa only [literalsBits_cons] using hS) hL hR hC hU hV hI hW hN hA
      have tail := ih b₁ a₁ none (u + 1)
        (by simp [b₁, outerBodyResult])
        (by simpa [b₁, outerBodyResult] using hL)
        (by simpa [b₁, outerBodyResult] using hR)
        (by simpa [b₁, outerBodyResult] using hC)
        (by simp [b₁, outerBodyResult])
        (by simpa [b₁, outerBodyResult] using hV)
        (by simpa [b₁, outerBodyResult] using hI)
        (by simpa [b₁, outerBodyResult] using hW)
        (by simpa [b₁, outerBodyResult] using hN)
        (by simp [a₁, outerBodyControl_slot, hA, Nat.add_mod])
      have run := Exec.loop_true (g := Action.peek Tape.input saveHead .done)
        (p := fun s : State => s.2.isSome)
        (d := Data.mk ((a, ()), register) base)
        (by simpa only [guardEq] using sourceNonempty)
        (by simpa only [guardEq, BooleanTapeCode.clean, a₁, b₁] using body) tail
      have result : outerLoopResult b₁ (u + 1) rest = outerLoopResult base u (left :: rest) := by
        funext tape
        cases tape <;> simp [outerLoopResult, b₁, outerBodyResult, suffixEdges,
          edgeRecords, List.flatMap_append, List.reverse_append, List.append_assoc,
          Nat.add_comm, Nat.add_left_comm]
      simpa only [outerLoop, outerLoopCost, outerControl, a₁, result] using run

theorem outerLoopCost_le (a : Control) (u B : Nat) (literals : List RawLiteral)
    (hU : u + literals.length ≤ B) (hS : (literalsBits literals).length ≤ B)
    (hL : ∀ left ∈ literals, left.1 ≤ B) :
    outerLoopCost a u literals ≤ literals.length * (40 * (B + 1) ^ 2 + 1) + 1 := by
  induction literals generalizing a u with
  | nil => simp [outerLoopCost]
  | cons left rest ih =>
      have tailSize : (literalsBits rest).length ≤ B := by
        rw [literalsBits_cons, List.length_append] at hS
        omega
      have hu : u + 1 + rest.length ≤ B := by simpa [List.length_cons, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hU
      have hb := outerBodyCost_le a left u B rest (hL left (by simp)) hu tailSize
        (fun x hx => hL x (by simp [hx]))
      have ht := ih (outerBodyControl a left rest) (u + 1) hu tailSize
        (fun x hx => hL x (by simp [hx]))
      simp only [outerLoopCost, List.length_cons]
      nlinarith

theorem skipField_exec (source : Tape) (base : Tape → List Bool) (s : State)
    (n : Nat) (suffix : List Bool) (hS : base source = encodeWord n ++ suffix) :
    Exec (skipField source) ⟨s, base⟩ (2 * n + 1)
      ⟨(s.1, some false), Function.update base source suffix⟩ := by
  induction n generalizing base s with
  | zero =>
      have run := Exec.loop_false (g := Action.pop source saveHead .done)
        (p := fun s : State => s.2.getD false) (a := skip) (d := Data.mk s base)
        (by simp [Action.eval, saveHead, hS, encodeWord])
      simpa [skipField, Action.eval, saveHead, hS, encodeWord] using run
  | succ n ih =>
      let b₁ := Function.update base source (encodeWord n ++ suffix)
      have guardEq : (Action.pop source saveHead .done).eval ⟨s, base⟩ =
          ⟨(s.1, some true), b₁⟩ := by
        simp [Action.eval, saveHead, hS, encodeWord, List.replicate_succ, b₁]
      have body : Exec skip ⟨(s.1, some true), b₁⟩ 1 ⟨(s.1, some true), b₁⟩ := Exec.atom .done _
      have tail := ih b₁ (s.1, some true) (by simp [b₁])
      have run := Exec.loop_true (g := Action.pop source saveHead .done)
        (p := fun s : State => s.2.getD false) (d := Data.mk s base)
        (by rw [guardEq]; rfl) (by simpa only [guardEq] using body) tail
      simpa [skipField, b₁, show 1 + (2 * n + 1) + 1 = 2 * (n + 1) + 1 by omega] using run

def countHeaderResult (base : Tape → List Bool) (m : Nat) (suffix : List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update base .input suffix) .unary
    (List.replicate (2 * m) true ++ base .unary)) .vertexCount
      (List.replicate (3 * m) true ++ base .vertexCount)

theorem countHeader_exec (base : Tape → List Bool) (s : State) (m : Nat)
    (suffix : List Bool) (hS : base .input = encodeWord m ++ suffix) :
    Exec countHeader ⟨s, base⟩ (2 * m + 1)
      ⟨(s.1, some false), countHeaderResult base m suffix⟩ := by
  induction m generalizing base s with
  | zero =>
      have run := Exec.loop_false (g := Action.pop Tape.input saveHead .done)
        (p := fun s : State => s.2.getD false)
        (a := Code.atom (.push .unary (fun _ => true) (.push .unary (fun _ => true)
          (.push .vertexCount (fun _ => true) (.push .vertexCount (fun _ => true)
            (.push .vertexCount (fun _ => true) .done))))))
        (d := Data.mk s base) (by simp [Action.eval, saveHead, hS, encodeWord])
      have result : countHeaderResult base 0 suffix = Function.update base Tape.input suffix := by
        funext tape
        cases tape <;> simp [countHeaderResult]
      simpa [countHeader, Action.eval, saveHead, hS, encodeWord, result] using run
  | succ m ih =>
      let b₀ := Function.update base Tape.input (encodeWord m ++ suffix)
      let b₁ := Function.update (Function.update b₀ Tape.unary (true :: true :: base .unary))
        Tape.vertexCount (true :: true :: true :: base .vertexCount)
      have guardEq : (Action.pop Tape.input saveHead .done).eval ⟨s, base⟩ =
          ⟨(s.1, some true), b₀⟩ := by
        simp [Action.eval, saveHead, hS, encodeWord, List.replicate_succ, b₀]
      have body := Exec.atom (.push Tape.unary (fun _ : State => true) (.push .unary (fun _ => true)
        (.push .vertexCount (fun _ => true) (.push .vertexCount (fun _ => true)
          (.push .vertexCount (fun _ => true) .done)))))
        (Data.mk (s.1, some true) b₀)
      have bodyEq : (Action.push Tape.unary (fun _ : State => true) (.push .unary (fun _ => true)
          (.push .vertexCount (fun _ => true) (.push .vertexCount (fun _ => true)
            (.push .vertexCount (fun _ => true) .done))))).eval ⟨(s.1, some true), b₀⟩ =
          ⟨(s.1, some true), b₁⟩ := by
        simp [Action.eval, b₁, b₀]
      rw [bodyEq] at body
      have tail := ih b₁ (s.1, some true) (by simp [b₁, b₀])
      have run := Exec.loop_true (g := Action.pop Tape.input saveHead .done)
        (p := fun s : State => s.2.getD false) (d := Data.mk s base)
        (by rw [guardEq]; rfl) (by simpa only [guardEq] using body) tail
      have unaryAppend : List.replicate (2 * m) true ++ true :: true :: base .unary =
          List.replicate (2 * (m + 1)) true ++ base .unary := by
        rw [show 2 * (m + 1) = 2 * m + 2 by omega, List.replicate_add]
        simp [List.append_assoc, List.replicate_succ]
      have vertexAppend : List.replicate (3 * m) true ++ true :: true :: true :: base .vertexCount =
          List.replicate (3 * (m + 1)) true ++ base .vertexCount := by
        rw [show 3 * (m + 1) = 3 * m + 3 by omega, List.replicate_add]
        simp [List.append_assoc, List.replicate_succ]
      have result : countHeaderResult b₁ m suffix = countHeaderResult base (m + 1) suffix := by
        funext tape
        cases tape <;> simp [countHeaderResult, b₁, b₀, unaryAppend, vertexAppend]
      simpa only [countHeader, result,
        show 1 + (2 * m + 1) + 1 = 2 * (m + 1) + 1 by omega] using run

def mainTapes (input accumulator index count unary output : List Bool) : Tape → List Bool
  | .input => input
  | .accumulator => accumulator
  | .outerIndex => index
  | .vertexCount => count
  | .unary => unary
  | .output => output
  | _ => []

@[simp] theorem mainTapes_input (i a x c u o next : List Bool) :
    Function.update (mainTapes i a x c u o) Tape.input next = mainTapes next a x c u o := by
  funext tape; cases tape <;> rfl

@[simp] theorem mainTapes_accumulator (i a x c u o next : List Bool) :
    Function.update (mainTapes i a x c u o) Tape.accumulator next = mainTapes i next x c u o := by
  funext tape; cases tape <;> rfl

@[simp] theorem mainTapes_outerIndex (i a x c u o next : List Bool) :
    Function.update (mainTapes i a x c u o) Tape.outerIndex next = mainTapes i a next c u o := by
  funext tape; cases tape <;> rfl

@[simp] theorem mainTapes_vertexCount (i a x c u o next : List Bool) :
    Function.update (mainTapes i a x c u o) Tape.vertexCount next = mainTapes i a x next u o := by
  funext tape; cases tape <;> rfl

@[simp] theorem mainTapes_unary (i a x c u o next : List Bool) :
    Function.update (mainTapes i a x c u o) Tape.unary next = mainTapes i a x c next o := by
  funext tape; cases tape <;> rfl

@[simp] theorem mainTapes_output (i a x c u o next : List Bool) :
    Function.update (mainTapes i a x c u o) Tape.output next = mainTapes i a x c u next := by
  funext tape; cases tape <;> rfl

@[simp] theorem mainTapes_scratch (i a x c u o : List Bool) :
    Function.update (mainTapes i a x c u o) Tape.scratch [] = mainTapes i a x c u o := by
  funext tape; cases tape <;> rfl

def rawInput («variables» clauses : Nat) (literals : List RawLiteral) : List Bool :=
  encodeWord «variables» ++ encodeWord clauses ++ literalsBits literals

def rawGraphWord (clauses : Nat) (literals : List RawLiteral) : List Bool :=
  BinaryEncoding.natBits (2 * clauses) ++ vertexRecords 0 (3 * clauses) ++ [false] ++
    edgeRecords (suffixEdges 0 literals) ++ [false]

def phaseCosts («variables» clauses : Nat) (literals : List RawLiteral) : List Nat :=
  [2 * «variables» + 1, 1, 2 * clauses + 1, 1,
    UnaryToBinaryMachine.steps (2 * clauses) 0,
    3 * (2 * clauses).bits.length + 3, (2 * clauses).bits.length + 1,
    vertexLoopCost (3 * clauses) 0, 1, (3 * clauses).bits.length + 1,
    outerLoopCost initialControl 0 literals, 1, literals.length.bits.length + 1,
    (rawGraphWord clauses literals).length + 1, 1]

def rawCost («variables» clauses : Nat) (literals : List RawLiteral) : Nat :=
  (phaseCosts «variables» clauses literals).sum + 1

theorem raw_program_exec («variables» clauses : Nat) (literals : List RawLiteral) :
    Exec program
      ⟨initialState, Function.update (fun _ => []) .input (rawInput «variables» clauses literals)⟩
      (rawCost «variables» clauses literals)
      ⟨initialState, Function.update (fun _ => []) .output (rawGraphWord clauses literals)⟩ := by
  let rest := literalsBits literals
  let header := BinaryEncoding.natBits (2 * clauses)
  let verts := vertexRecords 0 (3 * clauses)
  let edges := edgeRecords (suffixEdges 0 literals)
  let acc₁ := header.reverse
  let acc₂ := verts.reverse ++ acc₁
  let acc₃ := false :: acc₂
  let acc₄ := edges.reverse ++ acc₃
  let acc₅ := false :: acc₄
  let ar := outerControl initialControl literals
  have skipped := skipField_exec Tape.input
    (mainTapes (rawInput «variables» clauses literals) [] [] [] [] []) initialState «variables»
    (encodeWord clauses ++ rest) (by simp [mainTapes, rawInput, rest, List.append_assoc])
  simp only [mainTapes_input] at skipped
  have seeded : Exec (pushBit .unary false)
      ⟨(initialState.1, some false), mainTapes (encodeWord clauses ++ rest) [] [] [] [] []⟩ 1
      ⟨(initialState.1, some false), mainTapes (encodeWord clauses ++ rest) [] [] [] [false] []⟩ := by
    simpa [pushBit, Action.eval, mainTapes] using Exec.atom
      (Action.push Tape.unary (fun _ : State => false) .done)
      (Data.mk (initialState.1, some false)
        (mainTapes (encodeWord clauses ++ rest) [] [] [] [] []))
  have counted := countHeader_exec
    (mainTapes (encodeWord clauses ++ rest) [] [] [] [false] [])
    (initialState.1, some false) clauses rest rfl
  have countResultEq : countHeaderResult
      (mainTapes (encodeWord clauses ++ rest) [] [] [] [false] []) clauses rest =
      mainTapes rest [] [] (List.replicate (3 * clauses) true) (encodeWord (2 * clauses)) [] := by
    simp [countHeaderResult, mainTapes, encodeWord]
  rw [countResultEq] at counted
  have reset : Exec (.atom (.load resetHead .done))
      ⟨(initialState.1, some false),
        mainTapes rest [] [] (List.replicate (3 * clauses) true) (encodeWord (2 * clauses)) []⟩ 1
      ⟨initialState,
        mainTapes rest [] [] (List.replicate (3 * clauses) true) (encodeWord (2 * clauses)) []⟩ :=
    Exec.atom _ _
  have converted := BooleanTapeCode.convert_exec Tape.unary .outerIndex .scratch
    (by decide) (by decide) (by decide)
    (mainTapes rest [] [] (List.replicate (3 * clauses) true) [] [])
    initialControl (2 * clauses) 0 []
  simp only [UnaryToBinaryMachine.tapes, List.append_nil, Nat.zero_bits, Nat.zero_add,
    mainTapes_unary, mainTapes_outerIndex, mainTapes_scratch] at converted
  have emitted := BooleanTapeCode.frame_exec Tape.outerIndex .scratch .accumulator
    (by decide) (by decide) (by decide)
    (mainTapes rest [] (2 * clauses).bits (List.replicate (3 * clauses) true) [] [])
    rfl initialControl none
  simp only [mainTapes, List.append_nil, mainTapes_accumulator] at emitted
  have drained := BooleanTapeCode.drain_exec Tape.outerIndex
    (mainTapes rest acc₁ (2 * clauses).bits (List.replicate (3 * clauses) true) [] []) initialState
  simp only [mainTapes, mainTapes_outerIndex] at drained
  have vertexRun := vertices_exec
    (mainTapes rest acc₁ [] (List.replicate (3 * clauses) true) [] [])
    initialControl none (3 * clauses) 0 rfl rfl rfl rfl
  simp only [vertexResult, Nat.zero_add, mainTapes, mainTapes_vertexCount,
    mainTapes_outerIndex, mainTapes_accumulator] at vertexRun
  have vertexEnd : Exec (pushBit .accumulator false)
      ⟨initialState, mainTapes rest acc₂ (3 * clauses).bits [] [] []⟩ 1
      ⟨initialState, mainTapes rest acc₃ (3 * clauses).bits [] [] []⟩ := by
    simpa [pushBit, Action.eval, mainTapes, acc₃] using Exec.atom
      (Action.push Tape.accumulator (fun _ : State => false) .done)
      (Data.mk initialState (mainTapes rest acc₂ (3 * clauses).bits [] [] []))
  have resetIndex := BooleanTapeCode.drain_exec Tape.outerIndex
    (mainTapes rest acc₃ (3 * clauses).bits [] [] []) initialState
  simp only [mainTapes, mainTapes_outerIndex] at resetIndex
  have edgeRun := outerLoop_exec (mainTapes rest acc₃ [] [] [] []) initialControl none
    0 literals rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  simp only [outerLoopResult, Nat.zero_add, mainTapes, mainTapes_input,
    mainTapes_outerIndex, mainTapes_accumulator] at edgeRun
  have edgeEnd : Exec (pushBit .accumulator false)
      ⟨BooleanTapeCode.clean ar, mainTapes [] acc₄ literals.length.bits [] [] []⟩ 1
      ⟨BooleanTapeCode.clean ar, mainTapes [] acc₅ literals.length.bits [] [] []⟩ := by
    simpa [pushBit, Action.eval, mainTapes, acc₅] using Exec.atom
      (Action.push Tape.accumulator (fun _ : State => false) .done)
      (Data.mk (BooleanTapeCode.clean ar) (mainTapes [] acc₄ literals.length.bits [] [] []))
  have cleanIndex := BooleanTapeCode.drain_exec Tape.outerIndex
    (mainTapes [] acc₅ literals.length.bits [] [] []) (BooleanTapeCode.clean ar)
  simp only [mainTapes, mainTapes_outerIndex] at cleanIndex
  have outputRun := BooleanTapeCode.transfer_exec Tape.accumulator .output (by decide)
    (mainTapes [] acc₅ [] [] [] []) (BooleanTapeCode.clean ar)
  simp only [mainTapes, BinPackingGames.Reduction.MachineTransfer.tapesAt,
    mainTapes_accumulator, mainTapes_output, List.append_nil] at outputRun
  have accumulatorEq : acc₅ = (rawGraphWord clauses literals).reverse := by
    simp [acc₅, acc₄, acc₃, acc₂, acc₁, edges, verts, header, rawGraphWord,
      List.reverse_append, List.append_assoc]
  rw [accumulatorEq, List.length_reverse, List.reverse_reverse] at outputRun
  have outputJoined : Exec (BooleanTapeCode.transfer Tape.accumulator .output)
      ⟨((BooleanTapeCode.clean ar).1, none), mainTapes [] acc₅ [] [] [] []⟩
      ((rawGraphWord clauses literals).length + 1)
      ⟨BooleanTapeCode.clean ar, mainTapes [] [] [] [] [] (rawGraphWord clauses literals)⟩ := by
    simpa only [accumulatorEq, BooleanTapeCode.clean] using outputRun
  have cleanControl : Exec (.atom (.load (fun _ => initialState) .done))
      ⟨BooleanTapeCode.clean ar, mainTapes [] [] [] [] [] (rawGraphWord clauses literals)⟩ 1
      ⟨initialState, mainTapes [] [] [] [] [] (rawGraphWord clauses literals)⟩ := Exec.atom _ _
  have last : Exec skip
      ⟨initialState, mainTapes [] [] [] [] [] (rawGraphWord clauses literals)⟩ 1
      ⟨initialState, mainTapes [] [] [] [] [] (rawGraphWord clauses literals)⟩ := Exec.atom .done _
  have run := Exec.seq skipped (Exec.seq seeded (Exec.seq counted (Exec.seq reset
    (Exec.seq converted (Exec.seq emitted (Exec.seq drained (Exec.seq vertexRun
      (Exec.seq vertexEnd (Exec.seq resetIndex (Exec.seq edgeRun (Exec.seq edgeEnd
        (Exec.seq cleanIndex (Exec.seq outputJoined (Exec.seq cleanControl last))))))))))))))
  have initialTapesEq : mainTapes (rawInput «variables» clauses literals) [] [] [] [] [] =
      Function.update (fun _ => []) Tape.input (rawInput «variables» clauses literals) := by
    funext tape; cases tape <;> rfl
  have finalTapesEq : mainTapes [] [] [] [] [] (rawGraphWord clauses literals) =
      Function.update (fun _ => []) Tape.output (rawGraphWord clauses literals) := by
    funext tape; cases tape <;> rfl
  simpa only [program, sequence, skip, frame, drain, transfer, rawCost, phaseCosts,
    List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc, initialState,
    BooleanTapeCode.clean, BinaryEncoding.natBits, BinPackingCompleteness.BinaryEncoding.nameBits,
    initialTapesEq, finalTapesEq, rest, acc₁, acc₂, acc₃, acc₄, acc₅, ar, header, verts, edges] using run

end

open BinPackingGames.Foundations.Target BinPackingGames.Foundations.Complexity

def rawLiteral {n : Nat} (literal : Literal n) : RawLiteral :=
  (literal.variableIndex.val, literal.positive)

def clauseLiterals {n : Nat} (clause : Clause n) : List RawLiteral :=
  [rawLiteral clause[0], rawLiteral clause[1], rawLiteral clause[2]]

def formulaLiterals (F : Formula) : List RawLiteral :=
  F.clauses.flatMap clauseLiterals

@[simp] theorem clauseLiterals_length {n : Nat} (clause : Clause n) :
    (clauseLiterals clause).length = 3 := rfl

@[simp] theorem formulaLiterals_length (F : Formula) :
    (formulaLiterals F).length = 3 * F.clauses.length := by
  unfold formulaLiterals
  induction F.clauses with
  | nil => rfl
  | cons clause rest ih =>
      simp only [List.flatMap_cons, List.length_append, clauseLiterals_length,
        List.length_cons, ih]
      omega

private theorem clauseLiterals_bits {n : Nat} (clause : Clause n) :
    literalsBits (clauseLiterals clause) = encodeWords (clauseWords clause) := by
  simp [clauseLiterals, literalsBits, literalBits, rawLiteral, clauseWords,
    literalWords, encodeWords, List.append_assoc]

private theorem clausesLiterals_bits {n : Nat} (clauses : List (Clause n)) :
    literalsBits (clauses.flatMap clauseLiterals) =
      encodeWords (clauses.flatMap clauseWords) := by
  induction clauses with
  | nil => rfl
  | cons clause rest ih =>
      simp only [List.flatMap_cons, literalsBits, List.flatMap_append, encodeWords_append]
      change literalsBits (clauseLiterals clause) ++ literalsBits (rest.flatMap clauseLiterals) =
        encodeWords (clauseWords clause) ++ encodeWords (rest.flatMap clauseWords)
      rw [clauseLiterals_bits, ih]

theorem formulaBits_eq_formulaLiterals (F : Formula) :
    formulaBits F = encodeWord F.variables ++ encodeWord F.clauses.length ++
      literalsBits (formulaLiterals F) := by
  rw [formulaLiterals, clausesLiterals_bits]
  simp [formulaBits, formulaWords, encodeWords, List.append_assoc]

theorem literalSlots_le_formulaBits_length (F : Formula) :
    3 * F.clauses.length ≤ (formulaBits F).length := by
  have h := encodeWords_length (formulaWords F)
  have hs := formulaWords_length F
  unfold formulaBits
  omega

theorem formulaLiterals_eq_ofFn (F : Formula) :
    formulaLiterals F =
      List.ofFn (fun u : LiteralSlotGraph.Vertex F =>
        rawLiteral (LiteralSlotGraph.literal F u)) := by
  change F.clauses.flatMap clauseLiterals =
    List.ofFn (fun u : Fin (3 * F.clauses.length) =>
      rawLiteral (LiteralSlotGraph.literal F u))
  rw [List.ofFn_mul']
  have inner :
      (fun c : Fin F.clauses.length => List.ofFn (fun j : Fin 3 =>
        rawLiteral (LiteralSlotGraph.literal F (LiteralSlotGraph.index F c j)))) =
      (fun c : Fin F.clauses.length => clauseLiterals F.clauses[c]) := by
    funext c
    simp only [LiteralSlotGraph.literal_index]
    simp [clauseLiterals, List.ofFn_succ]
  change F.clauses.flatMap clauseLiterals =
    (List.ofFn (fun c : Fin F.clauses.length => List.ofFn (fun j : Fin 3 =>
      rawLiteral (LiteralSlotGraph.literal F (LiteralSlotGraph.index F c j))))).flatten
  rw [inner]
  simp only [Fin.getElem_fin]
  rw [List.ofFn_getElem_eq_map]
  induction F.clauses with
  | nil => rfl
  | cons clause rest ih => simp [ih]

private abbrev TaggedLiteral := Nat × RawLiteral

private def indexFrom (u : Nat) : List RawLiteral → List TaggedLiteral
  | [] => []
  | literal :: rest => (u, literal) :: indexFrom (u + 1) rest

private def taggedConflict (a b : TaggedLiteral) : Prop :=
  a.1 / 3 = b.1 / 3 ∨ (a.2.1 = b.2.1 ∧ a.2.2 ≠ b.2.2)

private instance (a b : TaggedLiteral) : Decidable (taggedConflict a b) := by
  unfold taggedConflict
  infer_instance

private def pairEntry (a b : TaggedLiteral) : Option (Nat × Nat) :=
  if a.1 < b.1 ∧ taggedConflict a b then some (a.1, b.1) else none

private def rowEntry (a b : TaggedLiteral) : Option (Nat × Nat) :=
  if taggedConflict a b then some (a.1, b.1) else none

private def forwardRows : List TaggedLiteral → List (Nat × Nat)
  | [] => []
  | a :: rest => rest.filterMap (rowEntry a) ++ forwardRows rest

private theorem rowEdges_eq_filterMap (u v : Nat) (left : RawLiteral)
    (xs : List RawLiteral) :
    rowEdges u v left xs = (indexFrom v xs).filterMap (rowEntry (u, left)) := by
  induction xs generalizing v with
  | nil => rfl
  | cons right rest ih =>
      simp only [rowEdges, indexFrom, List.filterMap_cons, rowEntry, taggedConflict]
      split_ifs with h <;> simp [h, ih]

private theorem suffixEdges_eq_forwardRows (u : Nat) (xs : List RawLiteral) :
    suffixEdges u xs = forwardRows (indexFrom u xs) := by
  induction xs generalizing u with
  | nil => rfl
  | cons literal rest ih =>
      simp only [suffixEdges, indexFrom, forwardRows, rowEdges_eq_filterMap, ih]

private theorem indexFrom_ofFn {n : Nat} (u : Nat) (f : Fin n → RawLiteral) :
    indexFrom u (List.ofFn f) = List.ofFn (fun i => (u + i.val, f i)) := by
  induction n generalizing u with
  | zero => simp [indexFrom]
  | succ n ih =>
      simp only [List.ofFn_succ, indexFrom, ih, Fin.val_zero, Nat.add_zero]
      congr 1
      apply congrArg List.ofFn
      funext i
      simp [Nat.add_comm, Nat.add_left_comm]

private theorem forwardRows_eq_allPairs (xs : List TaggedLiteral)
    (sorted : xs.Pairwise (fun a b => a.1 < b.1)) :
    forwardRows xs = xs.flatMap (fun a => xs.filterMap (pairEntry a)) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      rcases List.pairwise_cons.mp sorted with ⟨ahead, restSorted⟩
      have first : rest.filterMap (rowEntry a) = rest.filterMap (pairEntry a) := by
        apply List.filterMap_congr
        intro b hb
        simp [rowEntry, pairEntry, ahead b hb]
      have tails : rest.flatMap (fun b => (a :: rest).filterMap (pairEntry b)) =
          rest.flatMap (fun b => rest.filterMap (pairEntry b)) := by
        apply List.flatMap_congr
        intro b hb
        have hnot : ¬b.1 < a.1 := by have := ahead b hb; omega
        simp [pairEntry, hnot]
      rw [forwardRows, List.flatMap_cons, first, ih restSorted, tails]
      simp only [List.filterMap_cons, show pairEntry a a = none by simp [pairEntry]]

private theorem filtered_product (α : Type*) (select : α → α → Bool)
    (value : α → α → Nat × Nat) (xs ys : List α) :
    xs.flatMap (fun a => ys.filterMap
      (fun b => if select a b then some (value a b) else none)) =
    ((xs.product ys).filter (fun e => select e.1 e.2)).map (fun e => value e.1 e.2) := by
  have row (a : α) :
      ys.filterMap (fun b => if select a b then some (value a b) else none) =
        ((ys.map (fun b => (a, b))).filter (fun e => select e.1 e.2)).map
          (fun e => value e.1 e.2) := by
    induction ys with
    | nil => rfl
    | cons b tail ihy =>
        cases hs : select a b <;> simp [hs, ihy]
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      change
        ys.filterMap (fun b => if select a b then some (value a b) else none) ++
            rest.flatMap (fun a => ys.filterMap
              (fun b => if select a b then some (value a b) else none)) =
          (((ys.map (fun b => (a, b))) ++ rest.product ys).filter
            (fun e => select e.1 e.2)).map (fun e => value e.1 e.2)
      rw [List.filter_append, List.map_append, row a, ih]

private def tagVertex (F : Formula) (u : LiteralSlotGraph.Vertex F) : TaggedLiteral :=
  (u.val, rawLiteral (LiteralSlotGraph.literal F u))

private theorem tagVertex_conflict (F : Formula) (u v : LiteralSlotGraph.Vertex F) :
    taggedConflict (tagVertex F u) (tagVertex F v) ↔ LiteralSlotGraph.Conflict F u v := by
  simp [taggedConflict, tagVertex, rawLiteral, LiteralSlotGraph.Conflict,
    LiteralSlotGraph.occurrence, Fin.ext_iff]

theorem suffixEdges_formulaLiterals (F : Formula) :
    suffixEdges 0 (formulaLiterals F) = (LiteralSlotGraph.graph F).endpointPairs := by
  have tagged : indexFrom 0 (formulaLiterals F) =
      (List.finRange (LiteralSlotGraph.vertexCount F)).map (tagVertex F) := by
    rw [formulaLiterals_eq_ofFn, indexFrom_ofFn]
    simp only [Nat.zero_add]
    change List.ofFn (tagVertex F) = _
    exact List.ofFn_eq_map
  have sorted : ((List.finRange (LiteralSlotGraph.vertexCount F)).map
      (tagVertex F)).Pairwise (fun a b => a.1 < b.1) := by
    rw [← List.ofFn_eq_map, List.pairwise_ofFn]
    intro i j hij
    exact hij
  rw [suffixEdges_eq_forwardRows, tagged, forwardRows_eq_allPairs _ sorted]
  simp only [List.flatMap_map, List.filterMap_map, Function.comp_def]
  have pairEq (u v : LiteralSlotGraph.Vertex F) :
      pairEntry (tagVertex F u) (tagVertex F v) =
        if decide (u < v ∧ LiteralSlotGraph.Conflict F u v)
        then some (u.val, v.val) else none := by
    change (if u.val < v.val ∧ taggedConflict (tagVertex F u) (tagVertex F v)
        then some (u.val, v.val) else none) = _
    simp only [tagVertex_conflict, decide_eq_true_eq, Fin.lt_def]
  simp_rw [pairEq]
  rw [filtered_product]
  rfl

end BinPackingGap.LiteralSlotGraphMachine

end OAI
