import OAI.Computability.PerfectCompleteness.Machines.InitializationTemplateLemmas
import OAI.Computability.UniqueGames.Machines.MachineCopy
import OAI.Computability.UniqueGames.Reduction.MachineSubstitution

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.InputCellsMachine

open Turing PostfixModel InitializationTemplate
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)


variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

abbrev Ports (K : Type) := Fin 3 ↪ K
abbrev Alphabet (_ : K) := Bool

def tapes (p : Ports K) (base : K → List Bool) (input output count : List Bool) :
    K → List Bool :=
  Function.update (Function.update (Function.update base (p 0) input) (p 1) output) (p 2) count

@[simp] theorem tapes_input (p : Ports K) (base : K → List Bool)
    (input output count : List Bool) : tapes p base input output count (p 0) = input := by
  simp [tapes, p.injective.ne (by decide : (0 : Fin 3) ≠ 1),
    p.injective.ne (by decide : (0 : Fin 3) ≠ 2)]

@[simp] theorem tapes_output (p : Ports K) (base : K → List Bool)
    (input output count : List Bool) : tapes p base input output count (p 1) = output := by
  simp [tapes, p.injective.ne (by decide : (1 : Fin 3) ≠ 2)]

@[simp] theorem tapes_count (p : Ports K) (base : K → List Bool)
    (input output count : List Bool) : tapes p base input output count (p 2) = count := by
  simp [tapes]

theorem tapes_other (p : Ports K) (base : K → List Bool)
    (input output count : List Bool) (k : K) (hk : ∀ j, k ≠ p j) :
    tapes p base input output count k = base k := by
  simp [tapes, hk]

theorem update_input (p : Ports K) (base : K → List Bool)
    (input output count replacement : List Bool) :
    Function.update (tapes p base input output count) (p 0) replacement =
      tapes p base replacement output count := by
  funext k
  by_cases hk : ∃ j, p j = k
  · obtain ⟨j, rfl⟩ := hk
    fin_cases j <;> simp [tapes, p.injective.eq_iff]
  · have hn : ∀ j, k ≠ p j := fun j h => hk ⟨j, h.symm⟩
    simp [tapes, hn]

theorem update_output (p : Ports K) (base : K → List Bool)
    (input output count replacement : List Bool) :
    Function.update (tapes p base input output count) (p 1) replacement =
      tapes p base input replacement count := by
  funext k
  by_cases hk : ∃ j, p j = k
  · obtain ⟨j, rfl⟩ := hk
    fin_cases j <;> simp [tapes, p.injective.eq_iff]
  · have hn : ∀ j, k ≠ p j := fun j h => hk ⟨j, h.symm⟩
    simp [tapes, hn]

theorem update_count (p : Ports K) (base : K → List Bool)
    (input output count replacement : List Bool) :
    Function.update (tapes p base input output count) (p 2) replacement =
      tapes p base input output replacement := by
  simp [tapes]

abbrev TruthTable (A : Nat) := Bool → Fin A → Bool

def tableAt (table : TruthTable A) (bit : Bool) (i : Nat) : Bool :=
  if hi : i < A then table bit ⟨i, hi⟩ else false

def rowFrom (table : TruthTable A) (bit : Bool) (start count : Nat) : List Token :=
  forTokens count (fun j => [.const (tableAt table bit (start + j))])

def rowTokens (table : TruthTable A) (bit : Bool) : List Token := rowFrom table bit 0 A

def streamTokens (table : TruthTable A) (input : List Bool) : List Token :=
  input.flatMap (rowTokens table)

theorem rowFrom_succ (table : TruthTable A) (bit : Bool) (start count : Nat) :
    rowFrom table bit start (count + 1) =
      .const (tableAt table bit start) :: rowFrom table bit (start + 1) count := by
  simp only [rowFrom, forTokens_succ_first, Nat.add_zero, List.singleton_append]
  congr 1
  apply forTokens_congr
  intro j _
  simp only [Nat.add_assoc, Nat.add_comm 1 j]

@[simp] theorem rowFrom_length (table : TruthTable A) (bit : Bool) (start count : Nat) :
    (rowFrom table bit start count).length = count := by
  simpa only [rowFrom, Nat.mul_one] using
    forTokens_length_eq count (fun j => [.const (tableAt table bit (start + j))]) 1
      (fun _ _ => rfl)

@[simp] theorem streamTokens_length (table : TruthTable A) (input : List Bool) :
    (streamTokens table input).length = A * input.length := by
  induction input with
  | nil => simp [streamTokens]
  | cons bit input ih =>
    simp only [streamTokens, List.flatMap_cons, List.length_append, rowTokens,
      rowFrom_length, List.length_cons] at *
    rw [ih, Nat.mul_add, Nat.mul_one]
    omega

theorem streamTokens_eq_rows (table : TruthTable A) (input : List Bool) :
    streamTokens table input =
      (List.ofFn fun i : Fin input.length => rowTokens table input[i.val]).flatten := by
  rw [List.ofFn_getElem_eq_map]
  rfl

theorem tokenBits_cons (token : Token) (tokens : List Token) :
    tokenBits (token :: tokens) = token.bits ++ tokenBits tokens := by
  simp [tokenBits, tokenWords, Token.bits]

theorem tokenBits_append (first second : List Token) :
    tokenBits (first ++ second) = tokenBits first ++ tokenBits second := by
  simp [tokenBits, tokenWords]

inductive Label (symbols : Nat)
  | scan
  | emit (bit : Bool) (index : Fin (symbols + 1))
  deriving DecidableEq, Fintype

def statement (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ)
    (table : TruthTable A) : Label A → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .scan =>
      .pop (p 0) (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.goto fun state => label (.emit (state.2.getD false) 0))
          (.load (fun state => (state.1, none))
            (Reduction.MachineTransfer.exitAt (p 0) exit)))
  | .emit bit i =>
      if hi : i.val < A then
        pushWord (p 1) (Token.bits (.const (table bit ⟨i.val, hi⟩)))
          (.push (p 2) (fun _ => true)
            (.goto fun _ => label (.emit bit ⟨i.val + 1, by omega⟩)))
      else .load (fun state => (state.1, none)) (.goto fun _ => label .scan)

def Agrees (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)) : Prop :=
  ∀ l, program (label l) = statement p label exit table l

def EmitAgrees (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)) : Prop :=
  ∀ bit i, program (label (.emit bit i)) = statement p label exit table (.emit bit i)

theorem scanStep_nil (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) (base : K → List Bool)
    (output count : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some (label .scan), (ambient, register), tapes p base [] output count⟩ =
      some ⟨exit, (ambient, none), tapes p base [] output count⟩ := by
  change some (TM2.stepAux (program (label .scan)) _ _) = _
  rw [ha .scan]
  cases exit <;> simp [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt, update_input]

theorem scanStep_cons (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) (base : K → List Bool)
    (bit : Bool) (input output count : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some (label .scan), (ambient, register), tapes p base (bit :: input) output count⟩ =
      some ⟨some (label (.emit bit 0)), (ambient, some bit), tapes p base input output count⟩ := by
  change some (TM2.stepAux (program (label .scan)) _ _) = _
  rw [ha .scan]
  simp [statement, TM2.stepAux, update_input]

theorem emitStep (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : EmitAgrees p label exit table program) (base : K → List Bool)
    (bit : Bool) (i : Nat) (hi : i < A) (input output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some (label (.emit bit ⟨i, by omega⟩)), (ambient, register), tapes p base input output count⟩ =
      some ⟨some (label (.emit bit ⟨i + 1, by omega⟩)), (ambient, register),
        tapes p base input ((Token.bits (.const (tableAt table bit i))).reverse ++ output)
          (true :: count)⟩ := by
  change some (TM2.stepAux (program (label (.emit bit ⟨i, by omega⟩))) _ _) = _
  rw [ha bit ⟨i, by omega⟩]
  simp only [statement, dite_eq_left hi, stepAux_pushWord, TM2.stepAux,
    tapes_output, update_output, tapes_count, update_count, tableAt]

theorem finishRowStep (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : EmitAgrees p label exit table program) (base : K → List Bool)
    (bit : Bool) (input output count : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some (label (.emit bit ⟨A, by omega⟩)), (ambient, register), tapes p base input output count⟩ =
      some ⟨some (label .scan), (ambient, none), tapes p base input output count⟩ := by
  change some (TM2.stepAux (program (label (.emit bit ⟨A, by omega⟩))) _ _) = _
  rw [ha bit ⟨A, by omega⟩]
  simp [statement, TM2.stepAux]

theorem rowTrace (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : EmitAgrees p label exit table program) (base : K → List Bool)
    (bit : Bool) (start remaining : Nat) (hr : start + remaining = A)
    (input output count : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[remaining + 1]
      (some ⟨some (label (.emit bit ⟨start, by omega⟩)), (ambient, register),
        tapes p base input output count⟩) =
      some ⟨some (label .scan), (ambient, none), tapes p base input
        ((tokenBits (rowFrom table bit start remaining)).reverse ++ output)
        (List.replicate remaining true ++ count)⟩ := by
  induction remaining generalizing start output count register with
  | zero =>
    have hs : start = A := by omega
    subst start
    simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some,
      rowFrom, forTokens, tokenBits, tokenWords, List.flatMap_nil, encodeWords,
      List.reverse_nil, List.replicate_zero, List.nil_append] using
      finishRowStep p label exit table program ha base bit input output count ambient register
  | succ remaining ih =>
    have hs : start < A := by omega
    rw [Function.iterate_succ_apply]
    simp only [MachineComposition.advance_some]
    rw [emitStep p label exit table program ha base bit start hs]
    rw [ih (start + 1) (by omega)]
    rw [rowFrom_succ, tokenBits_cons, List.reverse_append]
    simp only [List.append_assoc, List.replicate_succ', List.singleton_append]

theorem streamTrace (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) (base : K → List Bool)
    (input output count : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[(A + 2) * input.length + 1]
      (some ⟨some (label .scan), (ambient, register), tapes p base input output count⟩) =
      some ⟨exit, (ambient, none), tapes p base []
        ((tokenBits (streamTokens table input)).reverse ++ output)
        (List.replicate (A * input.length) true ++ count)⟩ := by
  induction input generalizing output count register with
  | nil =>
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, streamTokens, List.flatMap_nil, tokenBits,
      tokenWords, encodeWords, List.reverse_nil, List.replicate_zero, List.nil_append] using
      scanStep_nil p label exit table program ha base output count ambient register
  | cons bit input ih =>
    have hround :
        (MachineComposition.advance (TM2.step program))^[A + 2]
          (some ⟨some (label .scan), (ambient, register), tapes p base (bit :: input) output count⟩) =
          some ⟨some (label .scan), (ambient, none), tapes p base input
            ((tokenBits (rowTokens table bit)).reverse ++ output)
            (List.replicate A true ++ count)⟩ := by
      change (MachineComposition.advance (TM2.step program))^[(A + 1) + 1] _ = _
      rw [Function.iterate_succ_apply]
      simp only [MachineComposition.advance_some]
      rw [scanStep_cons p label exit table program ha base]
      exact rowTrace p label exit table program (fun b i => ha (.emit b i)) base bit 0 A (by omega)
        input output count ambient (some bit)
    have htime : (A + 2) * (bit :: input).length + 1 =
        ((A + 2) * input.length + 1) + (A + 2) := by
      rw [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    rw [htime, Function.iterate_add_apply, hround, ih]
    simp only [streamTokens, List.flatMap_cons, tokenBits_append, List.reverse_append,
      List.append_assoc, List.length_cons, Nat.mul_add, Nat.mul_one]
    rw [List.replicate_add]
    simp only [List.append_assoc]

def streamInTime (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) (base : K → List Bool)
    (input output count : List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (label .scan), (ambient, register), tapes p base input output count⟩
      (some ⟨exit, (ambient, none), tapes p base []
        ((tokenBits (streamTokens table input)).reverse ++ output)
        (List.replicate (A * input.length) true ++ count)⟩)
      ((A + 2) * input.length + 1) where
  steps := (A + 2) * input.length + 1
  evals_in_steps := streamTrace p label exit table program ha base input output count ambient register
  steps_le_m := Nat.le_refl _

theorem copyAndStreamTrace (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ)
    (table : TruthTable A) (saved scratch : K)
    (hSaved : ∀ j, saved ≠ p j) (hScratch : ∀ j, scratch ≠ p j)
    (hSep : saved ≠ scratch) (copyFirst copySecond : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program)
    (atFirst : program copyFirst = Reduction.MachineTransfer.loopAt saved scratch
      id false copyFirst (some copySecond))
    (atSecond : program copySecond = MachineCopy.forkLoop scratch saved (p 0)
      false copySecond (some (label .scan)))
    (base : K → List Bool) (input output count : List Bool)
    (hinput : base saved = input) (hEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[(A + 4) * input.length + 3]
      (some ⟨some copyFirst, (ambient, register), tapes p base [] output count⟩) =
      some ⟨exit, (ambient, none), tapes p base []
        ((tokenBits (streamTokens table input)).reverse ++ output)
        (List.replicate (A * input.length) true ++ count)⟩ := by
  have hsource : tapes p base [] output count saved = input := by
    rw [tapes_other p base [] output count saved hSaved, hinput]
  have hscratch : tapes p base [] output count scratch = [] := by
    rw [tapes_other p base [] output count scratch hScratch, hEmpty]
  have hc := MachineCopy.copyTrace saved (p 0) scratch (hSaved 0) hSep
    (hScratch 0).symm false copyFirst copySecond (some (label .scan)) program
    atFirst atSecond (tapes p base [] output count) hscratch ambient register
  rw [hsource, tapes_input, List.append_nil, update_input] at hc
  have htime : (A + 4) * input.length + 3 =
      ((A + 2) * input.length + 1) + 2 * (input.length + 1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  rw [htime, Function.iterate_add_apply, hc]
  exact streamTrace p label exit table program ha base input output count ambient none

def program (table : TruthTable A) :
    Label A → TM2.Stmt (Alphabet (K := Fin 3)) (Label A) (Unit × Option Bool) :=
  statement (Function.Embedding.refl _) (Function.Embedding.refl _) none table

abbrev machine (table : TruthTable A) : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Label A
  main := .scan
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program table

def machineInTime (table : TruthTable A) (base : Fin 3 → List Bool)
    (input output count : List Bool) :
    StateTransition.EvalsToInTime (machine table).step
      ⟨some .scan, ((), none), tapes (Function.Embedding.refl _) base input output count⟩
      (some ⟨none, ((), none), tapes (Function.Embedding.refl _) base []
        ((tokenBits (streamTokens table input)).reverse ++ output)
        (List.replicate (A * input.length) true ++ count)⟩)
      ((A + 2) * input.length + 1) :=
  streamInTime (Function.Embedding.refl _) (Function.Embedding.refl _) none table
    (program table) (fun _ => rfl) base input output count () none

noncomputable section Verifier

open VerifierCircuit WitnessEncoding

local instance alphabetDecidable (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def symbolTruth (V : NPVerifier) (bit : Bool) :
    (Σ k, Option (V.computation.tm.Γ k)) → Bool
  | ⟨k, a⟩ => if h : k = V.computation.tm.k₀ then by
    subst k
    exact decide (some (V.computation.inputAlphabet.invFun bit) = a)
  else decide ((none : Option (V.computation.tm.Γ k)) = a)

def prefixTruth (V : NPVerifier) : TruthTable (indexing V).symbolCount := fun bit j =>
  symbolTruth V bit ((indexing V).symbols.symm j)

theorem symbolTruth_eq_initialCellTokens (V : NPVerifier) (input : List Bool) (S : Nat)
    (i : Fin S) (bit : Bool) (hi : i.val < (inputPrefix input).length)
    (hbit : (inputPrefix input)[i.val]? = some bit)
    (symbol : Σ k, Option (V.computation.tm.Γ k)) :
    [.const (symbolTruth V bit symbol)] = initialCellTokens V input S symbol.1 i symbol.2 := by
  obtain ⟨k, a⟩ := symbol
  by_cases hk : k = V.computation.tm.k₀
  · subst k
    simp only [symbolTruth, initialCellTokens, dite_true]
    simp only [inputCellTokens, ite_eq_left hi, hbit, Option.map_some]
  · simp [symbolTruth, initialCellTokens, hk]

theorem prefixTruth_eq_initialCellTokens (V : NPVerifier) (input : List Bool) (S : Nat)
    (i : Fin S) (bit : Bool) (hi : i.val < (inputPrefix input).length)
    (hbit : (inputPrefix input)[i.val]? = some bit) (j : Fin (indexing V).symbolCount) :
    [.const (prefixTruth V bit j)] =
      initialCellTokens V input S ((indexing V).symbols.symm j).1 i
        ((indexing V).symbols.symm j).2 :=
  symbolTruth_eq_initialCellTokens V input S i bit hi hbit ((indexing V).symbols.symm j)

theorem prefixRow_eq_initialCellTokens (V : NPVerifier) (input : List Bool) (S : Nat)
    (i : Fin S) (bit : Bool) (hi : i.val < (inputPrefix input).length)
    (hbit : (inputPrefix input)[i.val]? = some bit) :
    rowTokens (prefixTruth V) bit =
      (List.ofFn fun j : Fin (indexing V).symbolCount =>
        initialCellTokens V input S ((indexing V).symbols.symm j).1 i
          ((indexing V).symbols.symm j).2).flatten := by
  rw [rowTokens, rowFrom, forTokens_eq_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  simp only [Nat.zero_add, tableAt, dite_eq_left j.isLt]
  exact prefixTruth_eq_initialCellTokens V input S i bit hi hbit j

theorem prefixStream_eq_initialCells (V : NPVerifier) (input : List Bool) (S : Nat)
    (hS : (inputPrefix input).length ≤ S) :
    streamTokens (prefixTruth V) (inputPrefix input) =
      (List.ofFn fun i : Fin (inputPrefix input).length =>
        (List.ofFn fun j : Fin (indexing V).symbolCount =>
          initialCellTokens V input S ((indexing V).symbols.symm j).1
            ⟨i.val, Nat.lt_of_lt_of_le i.isLt hS⟩
            ((indexing V).symbols.symm j).2).flatten).flatten := by
  rw [streamTokens_eq_rows]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact prefixRow_eq_initialCellTokens V input S ⟨i.val, Nat.lt_of_lt_of_le i.isLt hS⟩
    (inputPrefix input)[i.val] i.isLt (List.getElem?_eq_getElem i.isLt)

end Verifier

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.InputCellsMachine


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.InputCellsCapacity

open Turing PostfixModel InputCellsMachine


variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

abbrev Ports (K : Type) := Fin 4 ↪ K

def corePorts (p : Ports K) : InputCellsMachine.Ports K where
  toFun j := p j.castSucc
  inj' := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin 4 => x.val) (p.injective h))

omit [DecidableEq K] in
theorem capacity_distinct (p : Ports K) (j : Fin 3) : p 3 ≠ corePorts p j := by
  intro h
  have hv := congrArg Fin.val (p.injective h)
  change 3 = j.val at hv
  omega

def tapes (p : Ports K) (base : K → List Bool) (remaining : Nat)
    (input output count : List Bool) : K → List Bool :=
  InputCellsMachine.tapes (corePorts p)
    (Function.update base (p 3) (encodeWord remaining)) input output count

@[simp] theorem tapes_input (p : Ports K) (base : K → List Bool) (remaining : Nat)
    (input output count : List Bool) : tapes p base remaining input output count (p 0) = input :=
  InputCellsMachine.tapes_input (corePorts p) _ _ _ _

@[simp] theorem tapes_output (p : Ports K) (base : K → List Bool) (remaining : Nat)
    (input output count : List Bool) : tapes p base remaining input output count (p 1) = output :=
  InputCellsMachine.tapes_output (corePorts p) _ _ _ _

@[simp] theorem tapes_count (p : Ports K) (base : K → List Bool) (remaining : Nat)
    (input output count : List Bool) : tapes p base remaining input output count (p 2) = count :=
  InputCellsMachine.tapes_count (corePorts p) _ _ _ _

@[simp] theorem tapes_capacity (p : Ports K) (base : K → List Bool) (remaining : Nat)
    (input output count : List Bool) :
    tapes p base remaining input output count (p 3) = encodeWord remaining := by
  rw [tapes, InputCellsMachine.tapes_other _ _ _ _ _ _ (capacity_distinct p)]
  simp

theorem tapes_other (p : Ports K) (base : K → List Bool) (remaining : Nat)
    (input output count : List Bool) (k : K) (hk : ∀ j, k ≠ p j) :
    tapes p base remaining input output count k = base k := by
  rw [tapes, InputCellsMachine.tapes_other _ _ _ _ _ _ (fun j => hk j.castSucc)]
  simp [hk]

theorem update_input (p : Ports K) (base : K → List Bool) (remaining : Nat)
    (input output count replacement : List Bool) :
    Function.update (tapes p base remaining input output count) (p 0) replacement =
      tapes p base remaining replacement output count :=
  InputCellsMachine.update_input (corePorts p) _ _ _ _ _

theorem update_capacity (p : Ports K) (base : K → List Bool) (remaining replacement : Nat)
    (input output count : List Bool) :
    Function.update (tapes p base remaining input output count) (p 3) (encodeWord replacement) =
      tapes p base replacement input output count := by
  funext k
  by_cases hk : ∃ j, p j = k
  · obtain ⟨j, rfl⟩ := hk
    fin_cases j <;> simp [p.injective.eq_iff]
  · have hn : ∀ j, k ≠ p j := fun j h => hk ⟨j, h.symm⟩
    simp [hn, tapes_other p base remaining input output count k hn,
      tapes_other p base replacement input output count k hn]

def statement (p : Ports K) (label : InputCellsMachine.Label A ↪ Λ) (exit : Option Λ)
    (table : TruthTable A) :
    InputCellsMachine.Label A → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .scan =>
      .pop (p 0) (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.pop (p 3) (fun state _ => state)
            (.goto fun state => label (.emit (state.2.getD false) 0)))
          (.load (fun state => (state.1, none))
            (Reduction.MachineTransfer.exitAt (p 0) exit)))
  | .emit bit i => InputCellsMachine.statement (corePorts p) label exit table (.emit bit i)

def Agrees (p : Ports K) (label : InputCellsMachine.Label A ↪ Λ) (exit : Option Λ)
    (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)) : Prop :=
  ∀ l, program (label l) = statement p label exit table l

omit [DecidableEq K] in
theorem emitAgrees (p : Ports K) (label : InputCellsMachine.Label A ↪ Λ) (exit : Option Λ)
    (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) :
    InputCellsMachine.EmitAgrees (corePorts p) label exit table program := by
  intro bit i
  exact ha (.emit bit i)

theorem scanStep_nil (p : Ports K) (label : InputCellsMachine.Label A ↪ Λ)
    (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) (base : K → List Bool) (remaining : Nat)
    (output count : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some (label .scan), (ambient, register), tapes p base remaining [] output count⟩ =
      some ⟨exit, (ambient, none), tapes p base remaining [] output count⟩ := by
  change some (TM2.stepAux (program (label .scan)) _ _) = _
  rw [ha .scan]
  cases exit <;> simp [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt, update_input]

theorem scanStep_cons (p : Ports K) (label : InputCellsMachine.Label A ↪ Λ)
    (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) (base : K → List Bool) (remaining : Nat)
    (bit : Bool) (input output count : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some (label .scan), (ambient, register), tapes p base (remaining + 1) (bit :: input) output count⟩ =
      some ⟨some (label (.emit bit 0)), (ambient, some bit),
        tapes p base remaining input output count⟩ := by
  change some (TM2.stepAux (program (label .scan)) _ _) = _
  rw [ha .scan]
  simp [statement, TM2.stepAux, update_input, encodeWord, List.replicate_succ]
  exact update_capacity p base (remaining + 1) remaining input output count

theorem streamTrace_add (p : Ports K) (label : InputCellsMachine.Label A ↪ Λ)
    (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) (base : K → List Bool) (remaining : Nat)
    (input output count : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[(A + 2) * input.length + 1]
      (some ⟨some (label .scan), (ambient, register),
        tapes p base (input.length + remaining) input output count⟩) =
      some ⟨exit, (ambient, none), tapes p base remaining []
        ((tokenBits (streamTokens table input)).reverse ++ output)
        (List.replicate (A * input.length) true ++ count)⟩ := by
  induction input generalizing output count register with
  | nil =>
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, streamTokens, List.flatMap_nil, tokenBits,
      tokenWords, encodeWords, List.reverse_nil, List.replicate_zero, List.nil_append] using
      scanStep_nil p label exit table program ha base remaining output count ambient register
  | cons bit input ih =>
    have hround :
        (MachineComposition.advance (TM2.step program))^[A + 2]
          (some ⟨some (label .scan), (ambient, register),
            tapes p base ((bit :: input).length + remaining) (bit :: input) output count⟩) =
          some ⟨some (label .scan), (ambient, none),
            tapes p base (input.length + remaining) input
              ((tokenBits (rowTokens table bit)).reverse ++ output)
              (List.replicate A true ++ count)⟩ := by
      have hn : (bit :: input).length + remaining = (input.length + remaining) + 1 := by
        simp only [List.length_cons]
        omega
      rw [hn]
      change (MachineComposition.advance (TM2.step program))^[(A + 1) + 1] _ = _
      rw [Function.iterate_succ_apply]
      simp only [MachineComposition.advance_some]
      rw [scanStep_cons p label exit table program ha base]
      exact rowTrace (corePorts p) label exit table program
        (emitAgrees p label exit table program ha)
        (Function.update base (p 3) (encodeWord (input.length + remaining))) bit 0 A (by omega)
        input output count ambient (some bit)
    have htime : (A + 2) * (bit :: input).length + 1 =
        ((A + 2) * input.length + 1) + (A + 2) := by
      rw [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    rw [htime, Function.iterate_add_apply, hround, ih]
    simp only [streamTokens, List.flatMap_cons, tokenBits_append, List.reverse_append,
      List.append_assoc, List.length_cons, Nat.mul_add, Nat.mul_one]
    rw [List.replicate_add]
    simp only [List.append_assoc]

theorem streamTrace (p : Ports K) (label : InputCellsMachine.Label A ↪ Λ)
    (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) (base : K → List Bool) (S : Nat)
    (input output count : List Bool) (hS : input.length ≤ S)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[(A + 2) * input.length + 1]
      (some ⟨some (label .scan), (ambient, register), tapes p base S input output count⟩) =
      some ⟨exit, (ambient, none), tapes p base (S - input.length) []
        ((tokenBits (streamTokens table input)).reverse ++ output)
        (List.replicate (A * input.length) true ++ count)⟩ := by
  have h := streamTrace_add p label exit table program ha base (S - input.length)
    input output count ambient register
  rw [Nat.add_sub_of_le hS] at h
  exact h

theorem copyAndStreamTrace (p : Ports K) (label : InputCellsMachine.Label A ↪ Λ)
    (exit : Option Λ) (table : TruthTable A) (saved scratch : K)
    (hSaved : ∀ j, saved ≠ p j) (hScratch : ∀ j, scratch ≠ p j)
    (hSep : saved ≠ scratch) (copyFirst copySecond : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program)
    (atFirst : program copyFirst = Reduction.MachineTransfer.loopAt saved scratch
      id false copyFirst (some copySecond))
    (atSecond : program copySecond = MachineCopy.forkLoop scratch saved (p 0)
      false copySecond (some (label .scan)))
    (base : K → List Bool) (S : Nat) (input output count : List Bool)
    (hS : input.length ≤ S) (hinput : base saved = input) (hEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[(A + 4) * input.length + 3]
      (some ⟨some copyFirst, (ambient, register), tapes p base S [] output count⟩) =
      some ⟨exit, (ambient, none), tapes p base (S - input.length) []
        ((tokenBits (streamTokens table input)).reverse ++ output)
        (List.replicate (A * input.length) true ++ count)⟩ := by
  have hsource : tapes p base S [] output count saved = input := by
    rw [tapes_other p base S [] output count saved hSaved, hinput]
  have hscratch : tapes p base S [] output count scratch = [] := by
    rw [tapes_other p base S [] output count scratch hScratch, hEmpty]
  have hc := MachineCopy.copyTrace saved (p 0) scratch (hSaved 0) hSep
    (hScratch 0).symm false copyFirst copySecond (some (label .scan)) program
    atFirst atSecond (tapes p base S [] output count) hscratch ambient register
  rw [hsource, tapes_input, List.append_nil, update_input] at hc
  have htime : (A + 4) * input.length + 3 =
      ((A + 2) * input.length + 1) + 2 * (input.length + 1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  rw [htime, Function.iterate_add_apply, hc]
  exact streamTrace p label exit table program ha base S input output count hS ambient none

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.InputCellsCapacity


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.CellsPrefixStage

open Turing PostfixModel InputCellsMachine


variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

abbrev Ports (K : Type) := Fin 7 ↪ K

def capacityPorts (p : Ports K) : InputCellsCapacity.Ports K where
  toFun j := p (![4, 2, 3, 5] j)
  inj' := by
    intro i j h
    have hmap : Function.Injective (fun j : Fin 4 => (![4, 2, 3, 5] j : Fin 7)) := by decide
    exact hmap (p.injective h)

omit [DecidableEq K] in
theorem saved_distinct (p : Ports K) (j : Fin 4) : p 0 ≠ capacityPorts p j := by
  change p 0 ≠ p (![4, 2, 3, 5] j)
  fin_cases j <;> simp [p.injective.eq_iff]

omit [DecidableEq K] in
theorem scratch_distinct (p : Ports K) (j : Fin 4) : p 6 ≠ capacityPorts p j := by
  change p 6 ≠ p (![4, 2, 3, 5] j)
  fin_cases j <;> simp [p.injective.eq_iff]

theorem prepared_eq (p : Ports K) (base : K → List Bool) (S : Nat)
    (hwork : base (p 4) = []) :
    InputCellsCapacity.tapes (capacityPorts p) base S [] (base (p 2)) (base (p 3)) =
      Function.update base (p 5) (encodeWord S) := by
  have hcore (q : InputCellsCapacity.Ports K) (j : Fin 3) :
      InputCellsCapacity.corePorts q j = q j.castSucc := by
    rw [InputCellsCapacity.corePorts.eq_1]
    rfl
  have hcapacity (j : Fin 4) : capacityPorts p j = p (![4, 2, 3, 5] j) := by
    rw [capacityPorts.eq_1]
    rfl
  funext k
  by_cases hk : ∃ j, p j = k
  · obtain ⟨j, rfl⟩ := hk
    fin_cases j <;>
      simp [InputCellsCapacity.tapes, InputCellsMachine.tapes,
        hcore, hcapacity, p.injective.eq_iff, hwork]
    change Function.update (_ : K → List Bool) (p 3) (base (p 3)) (p 3) = base (p 3)
    simp
  · have hn : ∀ j, k ≠ p j := fun j h => hk ⟨j, h.symm⟩
    simp [InputCellsCapacity.tapes, InputCellsMachine.tapes,
      hcore, hcapacity, hn]

inductive Label (symbols : Nat)
  | capacityFirst | capacitySecond | prefixFirst | prefixSecond
  | stream (entry : InputCellsMachine.Label symbols)
  deriving DecidableEq, Fintype

def streamLabels (label : Label A ↪ Λ) : InputCellsMachine.Label A ↪ Λ where
  toFun entry := label (.stream entry)
  inj' := by
    intro i j h
    exact Label.stream.inj (label.injective h)

def statement (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ)
    (table : TruthTable A) : Label A → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .capacityFirst => Reduction.MachineTransfer.loopAt (p 1) (p 6) id false
      (label .capacityFirst) (some (label .capacitySecond))
  | .capacitySecond => MachineCopy.forkLoop (p 6) (p 1) (p 5) false
      (label .capacitySecond) (some (label .prefixFirst))
  | .prefixFirst => Reduction.MachineTransfer.loopAt (p 0) (p 6) id false
      (label .prefixFirst) (some (label .prefixSecond))
  | .prefixSecond => MachineCopy.forkLoop (p 6) (p 0) (p 4) false
      (label .prefixSecond) (some (label (.stream .scan)))
  | .stream entry => InputCellsCapacity.statement (capacityPorts p) (streamLabels label)
      exit table entry

def Agrees (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ) (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)) : Prop :=
  ∀ entry, program (label entry) = statement p label exit table entry

omit [DecidableEq K] in
theorem stream_agrees (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ)
    (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) :
    InputCellsCapacity.Agrees (capacityPorts p) (streamLabels label) exit table program := by
  intro entry
  exact ha (.stream entry)

theorem trace (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ)
    (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) (base : K → List Bool)
    (input : List Bool) (S : Nat) (hS : input.length ≤ S)
    (hinput : base (p 0) = input) (hcached : base (p 1) = encodeWord S)
    (hwork : base (p 4) = []) (hcapacity : base (p 5) = []) (hscratch : base (p 6) = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * (S + 2) + ((A + 4) * input.length + 3)]
      (some ⟨some (label .capacityFirst), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), InputCellsCapacity.tapes (capacityPorts p) base
        (S - input.length) []
        ((tokenBits (streamTokens table input)).reverse ++ base (p 2))
        (List.replicate (A * input.length) true ++ base (p 3))⟩ := by
  have hc := MachineCopy.copyTrace (p 1) (p 5) (p 6)
    (p.injective.ne (by decide)) (p.injective.ne (by decide)) (p.injective.ne (by decide))
    false (label .capacityFirst) (label .capacitySecond) (some (label .prefixFirst))
    program (ha .capacityFirst) (ha .capacitySecond) base hscratch ambient register
  rw [hcached, hcapacity, List.append_nil, encodeWord_length] at hc
  have hp := InputCellsCapacity.copyAndStreamTrace (capacityPorts p) (streamLabels label)
    exit table (p 0) (p 6) (saved_distinct p) (scratch_distinct p)
    (p.injective.ne (by decide)) (label .prefixFirst) (label .prefixSecond) program
    (stream_agrees p label exit table program ha) (ha .prefixFirst) (ha .prefixSecond)
    base S input (base (p 2)) (base (p 3)) hS hinput hscratch ambient none
  rw [prepared_eq p base S hwork] at hp
  rw [Nat.add_comm (2 * (S + 2)), Function.iterate_add_apply, hc]
  exact hp

def inTime (p : Ports K) (label : Label A ↪ Λ) (exit : Option Λ)
    (table : TruthTable A)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (ha : Agrees p label exit table program) (base : K → List Bool)
    (input : List Bool) (S : Nat) (hS : input.length ≤ S)
    (hinput : base (p 0) = input) (hcached : base (p 1) = encodeWord S)
    (hwork : base (p 4) = []) (hcapacity : base (p 5) = []) (hscratch : base (p 6) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (label .capacityFirst), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), InputCellsCapacity.tapes (capacityPorts p) base
        (S - input.length) []
        ((tokenBits (streamTokens table input)).reverse ++ base (p 2))
        (List.replicate (A * input.length) true ++ base (p 3))⟩)
      (2 * (S + 2) + ((A + 4) * input.length + 3)) where
  steps := 2 * (S + 2) + ((A + 4) * input.length + 3)
  evals_in_steps := trace p label exit table program ha base input S hS hinput hcached
    hwork hcapacity hscratch ambient register
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.CellsPrefixStage

end OAI
