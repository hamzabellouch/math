import Mathlib
import OAI.Computability.DirectedFeedback.Encoding.Occurrences

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceBounds

open Target
open DFVSGames.Reduction

theorem formulaBits_length (F : Formula) :
    (Complexity.formulaBits F).length = F.«variables» + F.clauses.length + 2 +
      (Complexity.encodeWords (F.clauses.flatMap Complexity.clauseWords)).length := by
  simp only [Complexity.formulaBits, Complexity.formulaWords,
    Complexity.encodeWords_append, List.length_append, Complexity.encodeWords,
    Complexity.encodeWord_length, List.length_nil]
  omega

theorem formulaBits_length_ge_variables (F : Formula) :
    F.«variables» ≤ (Complexity.formulaBits F).length := by
  rw [formulaBits_length]
  omega

theorem formulaBits_length_ge_clauses (F : Formula) :
    F.clauses.length ≤ (Complexity.formulaBits F).length := by
  rw [formulaBits_length]
  omega

theorem formulaBits_length_ge_two (F : Formula) :
    2 ≤ (Complexity.formulaBits F).length := by
  rw [formulaBits_length]
  omega

def bitCountFormula (n m u : ℕ) : ℕ :=
  n ^ u * 2 ^ (2 ^ u) + m ^ u * 2 ^ (8 ^ u) + 1

def bitCoefficient (u : ℕ) : ℕ := 2 ^ (2 ^ u) + 2 ^ (8 ^ u) + 1

def testCoefficient (u D : ℕ) : ℕ :=
  3 ^ u * 2 ^ (2 ^ u) * D ^ (8 ^ u) * 2 ^ (8 ^ u)

def occurrenceCoefficient (u D : ℕ) : ℕ := testCoefficient u D + 1

theorem one_le_input_power (F : Formula) (u : ℕ) :
    1 ≤ (Complexity.formulaBits F).length ^ u := by
  apply Nat.one_le_pow
  have h := formulaBits_length_ge_two F
  omega

theorem bitCountFormula_le_input (F : Formula) (u : ℕ) :
    bitCountFormula F.«variables» F.clauses.length u ≤
      bitCoefficient u * (Complexity.formulaBits F).length ^ u := by
  have hn := Nat.pow_le_pow_left (formulaBits_length_ge_variables F) u
  have hm := Nat.pow_le_pow_left (formulaBits_length_ge_clauses F) u
  have hpos := one_le_input_power F u
  unfold bitCountFormula bitCoefficient
  calc
    _ ≤ (Complexity.formulaBits F).length ^ u * 2 ^ (2 ^ u) +
        (Complexity.formulaBits F).length ^ u * 2 ^ (8 ^ u) +
        (Complexity.formulaBits F).length ^ u :=
      Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_right _ hn) (Nat.mul_le_mul_right _ hm)) hpos
    _ = _ := by ring

theorem testCountFormula_le_input (F : Formula) (u D : ℕ) :
    (F.clauses.length * 3) ^ u * 2 ^ (2 ^ u) * D ^ (8 ^ u) * 2 ^ (8 ^ u) ≤
      testCoefficient u D * (Complexity.formulaBits F).length ^ u := by
  have hm := Nat.pow_le_pow_left (formulaBits_length_ge_clauses F) u
  calc
    _ = testCoefficient u D * F.clauses.length ^ u := by
      simp only [testCoefficient, Nat.mul_pow]
      ring
    _ ≤ _ := Nat.mul_le_mul_left _ hm

theorem testCountFormula_add_one_le_input (F : Formula) (u D : ℕ) :
    (F.clauses.length * 3) ^ u * 2 ^ (2 ^ u) * D ^ (8 ^ u) * 2 ^ (8 ^ u) + 1 ≤
      occurrenceCoefficient u D * (Complexity.formulaBits F).length ^ u := by
  calc
    _ ≤ testCoefficient u D * (Complexity.formulaBits F).length ^ u +
        (Complexity.formulaBits F).length ^ u :=
      Nat.add_le_add (testCountFormula_le_input F u D) (one_le_input_power F u)
    _ = _ := by simp only [occurrenceCoefficient, Nat.add_mul, Nat.one_mul]

def sourceSizeBound (V E u L : ℕ) : ℕ :=
  V * L ^ u + E * L ^ u + 2 + E * L ^ u * (3 * (V * L ^ u) + 2)

theorem sourceBits_length_le (input : SourceEncoding.Input) (V E u L : ℕ)
    (hv : input.«variables» ≤ V * L ^ u)
    (he : input.equations.length ≤ E * L ^ u) :
    (SourceEncoding.inputBits input).length ≤ sourceSizeBound V E u L := by
  apply (SourceEncoding.inputBits_length_le input).trans
  unfold sourceSizeBound
  exact Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add hv he) 2)
    (Nat.mul_le_mul he (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hv) 2))

noncomputable def sourcePolynomial (u D : ℕ) : Polynomial ℕ :=
  let V := Polynomial.C (bitCoefficient u) * Polynomial.X ^ u
  let E := Polynomial.C (occurrenceCoefficient u D) * Polynomial.X ^ u
  V + E + Polynomial.C 2 + E * (Polynomial.C 3 * V + Polynomial.C 2)

theorem sourcePolynomial_eval (u D L : ℕ) :
    (sourcePolynomial u D).eval L =
      sourceSizeBound (bitCoefficient u) (occurrenceCoefficient u D) u L := by
  simp [sourcePolynomial, sourceSizeBound]

open SourceOccurrences SourceContexts

theorem card_testTape (u D : ℕ) :
    Fintype.card (SourceTape.TestTape (I u) (J u) D) =
      2 ^ (2 ^ u) * (D ^ (8 ^ u) * 2 ^ (8 ^ u)) := by
  rw [SourceTape.card_testTape, card_I, card_J]

theorem testTapeEncoding_size (u D : ℕ) :
    (SourceOccurrences.testTapeEncoding u D).size =
      2 ^ (2 ^ u) * (D ^ (8 ^ u) * 2 ^ (8 ^ u)) := rfl

theorem card_sourceIndex (F : Formula) (u D : ℕ) :
    Fintype.card (SourceIndex F u D) =
      (F.clauses.length ^ u * 3 ^ u) *
        (2 ^ (2 ^ u) * (D ^ (8 ^ u) * 2 ^ (8 ^ u))) := by
  rw [(sourceIndexEncoding F u D).card_eq_size]
  rfl

theorem nBits_le_input (F : Formula) (u : ℕ) :
    nBits F u ≤ bitCoefficient u * (Complexity.formulaBits F).length ^ u := by
  have h := bitCountFormula_le_input F u
  simpa only [nBits_eq, bitCountFormula, Nat.add_assoc] using h

theorem rawSourceList_length_eq (F : Formula) (u D : ℕ) :
    (rawSourceList F u D).length = testCoefficient u D * F.clauses.length ^ u := by
  rw [rawSourceList_length]
  unfold testCoefficient
  ac_rfl

theorem rawSourceList_length_le_input (F : Formula) (u D : ℕ) :
    (rawSourceList F u D).length ≤
      testCoefficient u D * (Complexity.formulaBits F).length ^ u := by
  rw [rawSourceList_length_eq]
  exact Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (formulaBits_length_ge_clauses F) u)

theorem sourceList_length_le_input (F : Formula) (u D : ℕ) :
    (sourceList F u D).length ≤
      occurrenceCoefficient u D * (Complexity.formulaBits F).length ^ u := by
  calc
    _ ≤ (rawSourceList F u D).length + 1 := sourceList_length_le_raw_add_one F u D
    _ ≤ testCoefficient u D * (Complexity.formulaBits F).length ^ u +
        (Complexity.formulaBits F).length ^ u :=
      Nat.add_le_add (rawSourceList_length_le_input F u D) (one_le_input_power F u)
    _ = _ := by simp only [occurrenceCoefficient, Nat.add_mul, Nat.one_mul]

theorem sourceInput_bits_polynomial (F : Formula) (u D : ℕ) (hD : 0 < D) :
    (SourceEncoding.inputBits (sourceInput F u D hD)).length ≤
      (sourcePolynomial u D).eval (Complexity.formulaBits F).length := by
  rw [sourcePolynomial_eval]
  exact sourceBits_length_le (sourceInput F u D hD)
    (bitCoefficient u) (occurrenceCoefficient u D) u (Complexity.formulaBits F).length
    (nBits_le_input F u) (sourceList_length_le_input F u D)

theorem fixed_parameters_source_size (u D : ℕ) (hD : 0 < D) :
    ∃ p : Polynomial ℕ, ∀ F : Formula,
      (SourceEncoding.inputBits (sourceInput F u D hD)).length ≤
        p.eval (Complexity.formulaBits F).length :=
  ⟨sourcePolynomial u D, fun F => sourceInput_bits_polynomial F u D hD⟩

end DFVSGames.Foundations.Hastad.SourceBounds


namespace DFVSGames.Foundations.Complexity.MachineFieldProfile

open Turing

abbrev Profile (q : Nat) := Fin q → Fin q → Bool

def equalityProfile {q : Nat} (words : Fin q → List Bool) : Profile q :=
  fun i j => decide (words i = words j)

theorem equalityProfile_encodeWord {q : Nat} (names : Fin q → Nat) (i j : Fin q) :
    equalityProfile (fun k => encodeWord (names k)) i j = decide (names i = names j) := by
  have h : encodeWord (names i) = encodeWord (names j) ↔ names i = names j := by
    constructor
    · intro heq
      have hh := congrArg List.length heq
      simpa only [encodeWord_length, Nat.add_right_cancel_iff] using hh
    · rintro heq
      rw [heq]
  simp only [equalityProfile, h]

section Transport
variable {K Λ σ τ : Type} [DecidableEq K]

omit [DecidableEq K] in
theorem statement_roundtrip (e : σ ≃ τ)
    (q : TM2.Stmt (fun _ : K => Bool) Λ τ) :
    MachineControl.statement id e (MachineControl.statement id e.symm q) = q := by
  induction q <;> simp_all [MachineControl.statement]

def copyStateEquiv (σ : Type) :
    ((σ × Bool × Option Bool) × Option Bool) ≃ MachineCompare.State σ where
  toFun s := (s.1.1, s.1.2.1, s.1.2.2, s.2)
  invFun s := ((s.1, s.2.1, s.2.2.1), s.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def normalState (ambient : σ) : MachineCompare.State σ := (ambient, false, none, none)

def copyStatement (q : TM2.Stmt (fun _ : K => Bool) Λ
    ((σ × Bool × Option Bool) × Option Bool)) :
    TM2.Stmt (fun _ : K => Bool) Λ (MachineCompare.State σ) :=
  MachineControl.statement id (copyStateEquiv σ) q

def copyInCompareState (source destination scratch : K)
    (hSD : source ≠ destination) (hST : source ≠ scratch) (hDT : destination ≠ scratch)
    (firstLabel secondLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineCompare.State σ))
    (atFirst : program firstLabel = copyStatement
      (Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel)))
    (atSecond : program secondLabel = copyStatement
      (MachineCopy.forkLoop scratch source destination false secondLabel exit))
    (base : K → List Bool) (hScratch : base scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some firstLabel, normalState ambient, base⟩
      (some ⟨exit, normalState ambient,
        Function.update base destination (base source ++ base destination)⟩)
      (2 * ((base source).length + 1)) := by
  let e := copyStateEquiv σ
  let view := MachineControl.program (Equiv.refl Λ) e.symm program
  have hfirst : view firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel) := by
    dsimp [view, MachineControl.program]
    rw [atFirst]
    exact statement_roundtrip e.symm _
  have hsecond : view secondLabel =
      MachineCopy.forkLoop scratch source destination false secondLabel exit := by
    dsimp [view, MachineControl.program]
    rw [atSecond]
    exact statement_roundtrip e.symm _
  let run := MachineCopy.copyInTime source destination scratch hSD hST hDT false
    firstLabel secondLabel exit view hfirst hsecond base hScratch (ambient, false, none) none
  have hprogram : MachineControl.program (Equiv.refl Λ) e view = program := by
    funext label
    exact statement_roundtrip e (program label)
  have hsim (a b : TM2.Cfg (fun _ : K => Bool) Λ ((σ × Bool × Option Bool) × Option Bool))
      (hab : TM2.step view a = some b) :
      TM2.step program (MachineControl.configuration id e a) =
        some (MachineControl.configuration id e b) := by
    have hh := MachineControl.step_simulation (Equiv.refl Λ) e view a
    rw [hprogram, hab] at hh
    exact hh
  have lifted := MachineComposition.liftExecutionInTime (TM2.step view) (TM2.step program)
    (MachineControl.configuration id e) hsim run
  simpa [MachineControl.configuration, copyStateEquiv, normalState, e] using lifted

end Transport

section PreservedComparison
variable {K Λ σ : Type} [DecidableEq K]

def nonDestructiveCompareInTime (left right workLeft workRight scratch : K)
    (hleft : left ≠ workLeft ∧ left ≠ workRight ∧ left ≠ scratch)
    (hright : right ≠ workLeft ∧ right ≠ workRight ∧ right ≠ scratch)
    (hwork : workLeft ≠ workRight ∧ workLeft ≠ scratch ∧ workRight ≠ scratch)
    (leftFirst leftSecond rightFirst rightSecond compareLabel : Λ)
    (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineCompare.State σ))
    (atLeftFirst : program leftFirst = copyStatement
      (Reduction.MachineTransfer.loopAt left scratch id false leftFirst (some leftSecond)))
    (atLeftSecond : program leftSecond = copyStatement
      (MachineCopy.forkLoop scratch left workLeft false leftSecond (some rightFirst)))
    (atRightFirst : program rightFirst = copyStatement
      (Reduction.MachineTransfer.loopAt right scratch id false rightFirst (some rightSecond)))
    (atRightSecond : program rightSecond = copyStatement
      (MachineCopy.forkLoop scratch right workRight false rightSecond (some compareLabel)))
    (atCompare : program compareLabel =
      MachineCompare.loop workLeft workRight compareLabel equalExit differentExit)
    (base : K → List Bool) (hWL : base workLeft = []) (hWR : base workRight = [])
    (hScratch : base scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some leftFirst, normalState ambient, base⟩
      (some ⟨if base left = base right then equalExit else differentExit,
        normalState ambient, base⟩)
      (2 * ((base left).length + 1) + 2 * ((base right).length + 1) +
        max (base left).length (base right).length + 1) := by
  let t₁ := Function.update base workLeft (base left)
  let t₂ := Function.update t₁ workRight (base right)
  have h₁ := copyInCompareState left workLeft scratch hleft.1 hleft.2.2 hwork.2.1
    leftFirst leftSecond (some rightFirst) program atLeftFirst atLeftSecond base hScratch ambient
  simp only [hWL, List.append_nil] at h₁
  have hSR : t₁ right = base right := by simp [t₁, hright.1]
  have hDR : t₁ workRight = [] := by simp [t₁, Ne.symm hwork.1, hWR]
  have hTR : t₁ scratch = [] := by simp [t₁, Ne.symm hwork.2.1, hScratch]
  have h₂ := copyInCompareState right workRight scratch hright.2.1 hright.2.2 hwork.2.2
    rightFirst rightSecond (some compareLabel) program atRightFirst atRightSecond t₁ hTR ambient
  rw [hSR, hDR] at h₂
  simp only [List.append_nil] at h₂
  have hL : t₂ workLeft = base left := by simp [t₂, t₁, hwork.1]
  have hR : t₂ workRight = base right := by simp [t₂]
  have hrestore : Reduction.MachineTransfer.tapesAt workLeft workRight t₂ [] [] = base := by
    funext p
    by_cases hl : p = workLeft
    · subst p
      simp [Reduction.MachineTransfer.tapesAt, hwork.1, hWL]
    · by_cases hr : p = workRight
      · subst p
        simp [Reduction.MachineTransfer.tapesAt, hWR]
      · simp [Reduction.MachineTransfer.tapesAt, t₂, t₁, hl, hr]
  have h₃ := MachineCompare.compareInTime workLeft workRight hwork.1 compareLabel
    equalExit differentExit program atCompare t₂ ambient none none
  rw [hL, hR, hrestore] at h₃
  let h₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ h₁ h₂
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ h₁₂ h₃
  exact { toEvalsTo := run.toEvalsTo, steps_le_m := by have h := run.steps_le_m; omega }

end PreservedComparison


def setEntry {q : Nat} (profile : Profile q) (pair : Fin q × Fin q) (bit : Bool) : Profile q :=
  Function.update profile pair.1 (Function.update (profile pair.1) pair.2 bit)

theorem setEntry_apply {q : Nat} (profile : Profile q) (pair : Fin q × Fin q)
    (bit : Bool) (i j : Fin q) :
    setEntry profile pair bit i j = if (i, j) = pair then bit else profile i j := by
  rcases pair with ⟨a, b⟩
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp [setEntry, hi, hj]

def setExpected {q : Nat} (words : Fin q → List Bool) (profile : Profile q)
    (pair : Fin q × Fin q) : Profile q :=
  setEntry profile pair (equalityProfile words pair.1 pair.2)

def foldProfile {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) : Profile q := cells.foldl (setExpected words) initial

theorem foldProfile_apply {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) (i j : Fin q) :
    foldProfile words initial cells i j =
      if (i, j) ∈ cells then equalityProfile words i j else initial i j := by
  induction cells generalizing initial with
  | nil => rfl
  | cons pair rest ih =>
    change foldProfile words (setExpected words initial pair) rest i j = _
    rw [ih]
    by_cases hrest : (i, j) ∈ rest
    · simp [hrest]
    · by_cases hpair : (i, j) = pair
      · subst pair
        simp [hrest, setExpected, setEntry_apply]
      · simp [hrest, hpair, setExpected, setEntry_apply]

abbrev Tape (q : Nat) := Fin q ⊕ Fin 3
abbrev Label {q : Nat} (cells : List (Fin q × Fin q)) := Fin (cells.length + 1) × Fin 7

def labelAt {q : Nat} (cells : List (Fin q × Fin q)) (r : Nat) (phase : Fin 7) : Label cells :=
  (⟨min r cells.length, by omega⟩, phase)

def storePair {q : Nat} (pair : Fin q × Fin q) (bit : Bool)
    {Λ : Type} (nextLabel : Λ) :
    TM2.Stmt (fun _ : Tape q => Bool) Λ (MachineCompare.State (Profile q)) :=
  .load (fun state => normalState (setEntry state.1 pair bit)) (.goto fun _ => nextLabel)

def profileProgram {q : Nat} (cells : List (Fin q × Fin q)) (label : Label cells) :
    TM2.Stmt (fun _ : Tape q => Bool) (Label cells) (MachineCompare.State (Profile q)) :=
  if h : label.1.val < cells.length then
    let pair := cells[label.1.val]
    let r := label.1.val
    match label.2.val with
    | 0 => copyStatement (Reduction.MachineTransfer.loopAt (.inl pair.1) (.inr 2) id false
        (labelAt cells r 0) (some (labelAt cells r 1)))
    | 1 => copyStatement (MachineCopy.forkLoop (.inr 2) (.inl pair.1) (.inr 0) false
        (labelAt cells r 1) (some (labelAt cells r 2)))
    | 2 => copyStatement (Reduction.MachineTransfer.loopAt (.inl pair.2) (.inr 2) id false
        (labelAt cells r 2) (some (labelAt cells r 3)))
    | 3 => copyStatement (MachineCopy.forkLoop (.inr 2) (.inl pair.2) (.inr 1) false
        (labelAt cells r 3) (some (labelAt cells r 4)))
    | 4 => MachineCompare.loop (.inr 0) (.inr 1) (labelAt cells r 4)
        (some (labelAt cells r 5)) (some (labelAt cells r 6))
    | 5 => storePair pair true (labelAt cells (r + 1) 0)
    | _ => storePair pair false (labelAt cells (r + 1) 0)
  else .halt

def pairTime {q : Nat} (words : Fin q → List Bool) (pair : Fin q × Fin q) : Nat :=
  2 * ((words pair.1).length + 1) + 2 * ((words pair.2).length + 1) +
    max (words pair.1).length (words pair.2).length + 2

def prefixProfile {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) (r : Nat) : Profile q :=
  foldProfile words initial (cells.take r)

def prefixTime {q : Nat} (words : Fin q → List Bool)
    (cells : List (Fin q × Fin q)) (r : Nat) : Nat :=
  ((cells.take r).map (pairTime words)).sum

theorem prefixProfile_succ {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) (r : Nat) (hr : r < cells.length) :
    prefixProfile words initial cells (r + 1) =
      setExpected words (prefixProfile words initial cells r) cells[r] := by
  unfold prefixProfile foldProfile
  rw [List.take_succ_eq_append_getElem hr, List.foldl_append]
  rfl

theorem prefixTime_succ {q : Nat} (words : Fin q → List Bool)
    (cells : List (Fin q × Fin q)) (r : Nat) (hr : r < cells.length) :
    prefixTime words cells (r + 1) = prefixTime words cells r + pairTime words cells[r] := by
  unfold prefixTime
  rw [List.take_succ_eq_append_getElem hr, List.map_append, List.sum_append]
  rfl

def stageInTime {q : Nat} (cells : List (Fin q × Fin q)) (r : Nat) (hr : r < cells.length)
    (base : Tape q → List Bool) (hwork : ∀ w : Fin 3, base (.inr w) = []) (profile : Profile q) :
    StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨some (labelAt cells r 0), normalState profile, base⟩
      (some ⟨some (labelAt cells (r + 1) 0),
        normalState (setExpected (fun i => base (.inl i)) profile cells[r]), base⟩)
      (pairTime (fun i => base (.inl i)) cells[r]) := by
  let pair := cells[r]
  have copied := nonDestructiveCompareInTime (.inl pair.1) (.inl pair.2)
    (.inr 0 : Tape q) (.inr 1) (.inr 2) (by simp) (by simp) (by simp)
    (labelAt cells r 0) (labelAt cells r 1) (labelAt cells r 2) (labelAt cells r 3)
    (labelAt cells r 4) (some (labelAt cells r 5)) (some (labelAt cells r 6))
    (profileProgram cells)
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr, pair])
    (by simp [profileProgram, labelAt, Nat.min_eq_left hr.le, hr])
    base (hwork 0) (hwork 1) (hwork 2) profile
  have stored : StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨if base (.inl pair.1) = base (.inl pair.2) then some (labelAt cells r 5)
        else some (labelAt cells r 6), normalState profile, base⟩
      (some ⟨some (labelAt cells (r + 1) 0),
        normalState (setExpected (fun i => base (.inl i)) profile pair), base⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change TM2.step (profileProgram cells)
        ⟨if base (.inl pair.1) = base (.inl pair.2) then some (labelAt cells r 5)
          else some (labelAt cells r 6), normalState profile, base⟩ = _
      by_cases heq : base (.inl pair.1) = base (.inl pair.2)
      · simp [heq, TM2.step, profileProgram, labelAt,
          Nat.min_eq_left hr.le, hr, storePair, TM2.stepAux, normalState,
          setExpected, equalityProfile, pair]
      · simp [heq, TM2.step, profileProgram, labelAt,
          Nat.min_eq_left hr.le, hr, storePair, TM2.stepAux, normalState,
          setExpected, equalityProfile, pair]
    steps_le_m := Nat.le_refl _
  }
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ copied stored
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have h := run.steps_le_m
  dsimp only [pair] at h
  dsimp only [pairTime]
  omega

def prefixInTime {q : Nat} (cells : List (Fin q × Fin q))
    (base : Tape q → List Bool) (hwork : ∀ w : Fin 3, base (.inr w) = []) (initial : Profile q)
    (r : Nat) (hr : r ≤ cells.length) :
    StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨some (labelAt cells 0 0), normalState initial, base⟩
      (some ⟨some (labelAt cells r 0),
        normalState (prefixProfile (fun i => base (.inl i)) initial cells r), base⟩)
      (prefixTime (fun i => base (.inl i)) cells r) := by
  induction r with
  | zero =>
    exact { steps := 0, evals_in_steps := rfl, steps_le_m := Nat.le_refl _ }
  | succ r ih =>
    have hrl : r < cells.length := by omega
    let first := ih (by omega)
    let second := stageInTime cells r hrl base hwork
      (prefixProfile (fun i => base (.inl i)) initial cells r)
    let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
    rw [prefixProfile_succ _ _ _ _ hrl, prefixTime_succ _ _ _ hrl]
    exact { toEvalsTo := run.toEvalsTo, steps_le_m := by have h := run.steps_le_m; omega }

def allPairs (q : Nat) : List (Fin q × Fin q) :=
  (List.finRange q).flatMap fun i => (List.finRange q).map fun j => (i, j)

theorem mem_allPairs {q : Nat} (i j : Fin q) : (i, j) ∈ allPairs q := by
  simp [allPairs]

theorem length_allPairs (q : Nat) : (allPairs q).length = q * q := by
  simp [allPairs, List.length_flatMap]

theorem foldProfile_allPairs {q : Nat} (words : Fin q → List Bool) (initial : Profile q) :
    foldProfile words initial (allPairs q) = equalityProfile words := by
  funext i j
  simp [foldProfile_apply, mem_allPairs]

def profileMachine (q : Nat) : FinTM2 where
  K := Tape q
  k₀ := .inr 0
  k₁ := .inr 0
  Γ _ := Bool
  Λ := Label (allPairs q)
  main := labelAt (allPairs q) 0 0
  σ := MachineCompare.State (Profile q)
  initialState := normalState (fun _ _ => false)
  m := profileProgram (allPairs q)

def profileInTime (q : Nat) (base : Tape q → List Bool)
    (hwork : ∀ w : Fin 3, base (.inr w) = []) (initial : Profile q) :
    StateTransition.EvalsToInTime (profileMachine q).step
      ⟨some (labelAt (allPairs q) 0 0), normalState initial, base⟩
      (some ⟨none, normalState (equalityProfile (fun i => base (.inl i))), base⟩)
      (((allPairs q).map (pairTime (fun i => base (.inl i)))).sum + 1) := by
  let cells := allPairs q
  have first := prefixInTime cells base hwork initial cells.length (Nat.le_refl _)
  have last : StateTransition.EvalsToInTime (TM2.step (profileProgram cells))
      ⟨some (labelAt cells cells.length 0),
        normalState (prefixProfile (fun i => base (.inl i)) initial cells cells.length), base⟩
      (some ⟨none, normalState (equalityProfile (fun i => base (.inl i))), base⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change TM2.step (profileProgram cells)
        ⟨some (labelAt cells cells.length 0),
          normalState (prefixProfile (fun i => base (.inl i)) initial cells cells.length), base⟩ = _
      simp [TM2.step, profileProgram, labelAt, TM2.stepAux,
        prefixProfile, cells, foldProfile_allPairs]
    steps_le_m := Nat.le_refl _
  }
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first last
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have h := run.steps_le_m
  simpa [prefixTime, cells, Nat.add_comm] using h

theorem pairTime_le {q : Nat} (words : Fin q → List Bool) (L : Nat)
    (hL : ∀ i, (words i).length ≤ L) (pair : Fin q × Fin q) :
    pairTime words pair ≤ 5 * L + 6 := by
  have hi := hL pair.1
  have hj := hL pair.2
  have hm := max_le hi hj
  dsimp only [pairTime]
  omega

theorem totalTime_le {q : Nat} (words : Fin q → List Bool) (L : Nat)
    (hL : ∀ i, (words i).length ≤ L) (cells : List (Fin q × Fin q)) :
    (cells.map (pairTime words)).sum ≤ cells.length * (5 * L + 6) := by
  induction cells with
  | nil => simp
  | cons pair rest ih =>
    have hp := pairTime_le words L hL pair
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

def profileInTime_bounded (q : Nat) (base : Tape q → List Bool)
    (hwork : ∀ w : Fin 3, base (.inr w) = []) (initial : Profile q)
    (L : Nat) (hL : ∀ i, (base (.inl i)).length ≤ L) :
    StateTransition.EvalsToInTime (profileMachine q).step
      ⟨some (labelAt (allPairs q) 0 0), normalState initial, base⟩
      (some ⟨none, normalState (equalityProfile (fun i => base (.inl i))), base⟩)
      (q * q * (5 * L + 6) + 1) := by
  let run := profileInTime q base hwork initial
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  apply run.steps_le_m.trans
  apply Nat.add_le_add_right
  simpa only [length_allPairs] using totalTime_le (fun i => base (.inl i)) L hL (allPairs q)


end DFVSGames.Foundations.Complexity.MachineFieldProfile


namespace DFVSGames.Foundations.Hastad.SourceProfileBridge

open Target SourceContexts SourceOccurrences SourceLocalSignature
open Complexity

def positionEncoding (u : ℕ) : Encoding (Position u) :=
  (Encoding.fin u).prod slotEncoding

def names (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    Fin (positionEncoding u).size → ℕ :=
  fun i => (occurrenceName F c ((positionEncoding u).code.symm i)).val

def nameWords (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    Fin (positionEncoding u).size → List Bool :=
  fun i => encodeWord (names F c i)

def reindexProfile (u : ℕ) (profile : MachineFieldProfile.Profile (positionEncoding u).size) :
    NameProfile u :=
  fun p q => profile ((positionEncoding u).code p) ((positionEncoding u).code q)

theorem computed_profile_eq (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    reindexProfile u (MachineFieldProfile.equalityProfile (nameWords F c)) =
      contextNameProfile F c := by
  funext p q
  unfold reindexProfile nameWords
  rw [MachineFieldProfile.equalityProfile_encodeWord]
  simp only [names, Equiv.symm_apply_apply, contextNameProfile, Fin.ext_iff]

theorem prepared_signature_eq (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) :
    (⟨fun p => positiveAt (PCP.clauseAt F (c p.1)) p.2,
      reindexProfile u (MachineFieldProfile.equalityProfile (nameWords F c)), s⟩ :
        Signature u) = ofContext F c s := by
  rw [computed_profile_eq]
  rfl

theorem nameWords_length_le_input (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (i : Fin (positionEncoding u).size) :
    (nameWords F c i).length ≤ (formulaBits F).length := by
  rw [nameWords, encodeWord_length]
  exact (Nat.succ_le_of_lt
    (occurrenceName F c ((positionEncoding u).code.symm i)).isLt).trans
      (SourceBounds.formulaBits_length_ge_variables F)

end DFVSGames.Foundations.Hastad.SourceProfileBridge


namespace DFVSGames.Foundations.Hastad.SourceSignLoad

open Turing
open SourceLocalSignature
open DFVSGames.Foundations.Complexity

def positions (u : ℕ) : List (Position u) :=
  ((SourceOccurrences.Encoding.fin u).prod SourceOccurrences.slotEncoding).enumerate

theorem mem_positions {u : ℕ} (p : Position u) : p ∈ positions u :=
  SourceOccurrences.Encoding.mem_enumerate _ p

def fillSigns {u : ℕ} (values initial : Position u → Bool)
    (cells : List (Position u)) : Position u → Bool :=
  cells.foldl (fun signs p => Function.update signs p (values p)) initial

theorem fillSigns_apply {u : ℕ} (values initial : Position u → Bool)
    (cells : List (Position u)) (p : Position u) :
    fillSigns values initial cells p = if p ∈ cells then values p else initial p := by
  induction cells generalizing initial with
  | nil => simp [fillSigns]
  | cons q cells ih =>
    change fillSigns values (Function.update initial q (values q)) cells p = _
    rw [ih]
    by_cases hp : p ∈ cells
    · simp [hp]
    · by_cases hpq : p = q
      · subst q; simp [hp]
      · simp [hp, hpq]

theorem fillSigns_positions {u : ℕ} (values initial : Position u → Bool) :
    fillSigns values initial (positions u) = values := by
  funext p
  rw [fillSigns_apply]
  simp only [mem_positions, ↓reduceIte]


variable {u : ℕ} {K Λ τ : Type} [DecidableEq K]

abbrev State (u : ℕ) (τ : Type) := Signature u × τ
abbrev Alphabet (_ : K) := Bool

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State u τ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def peekChain (field : Position u → K) (exit : Option Λ) :
    List (Position u) → TM2.Stmt (Alphabet (K := K)) Λ (State u τ)
  | [] => finish exit
  | p :: rest =>
    .peek (field p) (fun state head =>
      ({state.1 with signs := Function.update state.1.signs p (head.getD false)}, state.2))
      (peekChain field exit rest)

def statement (field : Position u → K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State u τ) :=
  peekChain field exit (positions u)

def readSigns (field : Position u → K) (tapes : K → List Bool) : Position u → Bool :=
  fun p => (tapes (field p)).head?.getD false

theorem stepAux_peekChain (field : Position u → K) (exit : Option Λ)
    (cells : List (Position u)) (initial : Signature u) (ambient : τ)
    (tapes : K → List Bool) :
    TM2.stepAux (peekChain field exit cells) (initial, ambient) tapes =
      ⟨exit, ({initial with signs := fillSigns (readSigns field tapes) initial.signs cells},
        ambient), tapes⟩ := by
  induction cells generalizing initial with
  | nil => cases exit <;> rfl
  | cons p rest ih =>
    simp only [peekChain, TM2.stepAux]
    rw [ih]
    rfl

theorem stepAux_statement (field : Position u → K) (exit : Option Λ)
    (initial : Signature u) (ambient : τ) (tapes : K → List Bool) :
    TM2.stepAux (statement field exit) (initial, ambient) tapes =
      ⟨exit, ({initial with signs := readSigns field tapes}, ambient), tapes⟩ := by
  rw [statement, stepAux_peekChain, fillSigns_positions]

omit [DecidableEq K] in
theorem peekChain_pushBound (field : Position u → K) (exit : Option Λ)
    (cells : List (Position u)) :
    Runtime.statementPushBound (peekChain (τ := τ) field exit cells) = 0 := by
  induction cells with
  | nil => cases exit <;> rfl
  | cons p rest ih => exact ih

omit [DecidableEq K] in
theorem statement_pushBound (field : Position u → K) (exit : Option Λ) :
    Runtime.statementPushBound (statement (τ := τ) field exit) = 0 :=
  peekChain_pushBound field exit (positions u)

omit [DecidableEq K] in
theorem readSigns_of_unary (field : Position u → K) (tapes : K → List Bool)
    (values : Position u → Bool) (suffix : Position u → List Bool)
    (hfields : ∀ p, tapes (field p) = encodeWord (if values p then 1 else 0) ++ suffix p) :
    readSigns field tapes = values := by
  funext p
  rw [readSigns, hfields]
  cases values p <;> rfl

theorem loadStep (field : Position u → K) (entryLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State u τ))
    (atEntry : program entryLabel = statement field exit)
    (initial : Signature u) (ambient : τ) (tapes : K → List Bool)
    (values : Position u → Bool) (suffix : Position u → List Bool)
    (hfields : ∀ p, tapes (field p) = encodeWord (if values p then 1 else 0) ++ suffix p) :
    TM2.step program ⟨some entryLabel, (initial, ambient), tapes⟩ =
      some ⟨exit, ({initial with signs := values}, ambient), tapes⟩ := by
  change some (TM2.stepAux (program entryLabel) (initial, ambient) tapes) = _
  rw [atEntry, stepAux_statement, readSigns_of_unary field tapes values suffix hfields]

def loadInTime (field : Position u → K) (entryLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State u τ))
    (atEntry : program entryLabel = statement field exit)
    (initial : Signature u) (ambient : τ) (tapes : K → List Bool)
    (values : Position u → Bool) (suffix : Position u → List Bool)
    (hfields : ∀ p, tapes (field p) = encodeWord (if values p then 1 else 0) ++ suffix p) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some entryLabel, (initial, ambient), tapes⟩
      (some ⟨exit, ({initial with signs := values}, ambient), tapes⟩) 1 where
  steps := 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[1] _ = _
    simpa only [Function.iterate_one, MachineComposition.advance_some] using
      loadStep field entryLabel exit program atEntry initial ambient tapes values suffix hfields
  steps_le_m := Nat.le_refl _

omit [DecidableEq K] in

theorem loaded_ofContext (F : Target.Formula) (c : SourceContexts.ClauseContext F u)
    (selected : SourceContexts.SlotContext u) (initial : Signature u)
    (hnames : initial.sameName = contextNameProfile F c)
    (hselected : initial.selected = selected) :
    {initial with signs := (ofContext F c selected).signs} = ofContext F c selected := by
  cases initial with
  | mk signs sameName chosen =>
    dsimp only at hnames hselected
    cases hnames
    cases hselected
    rfl

def loadContextInTime (F : Target.Formula) (c : SourceContexts.ClauseContext F u)
    (selected : SourceContexts.SlotContext u) (field : Position u → K)
    (entryLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State u τ))
    (atEntry : program entryLabel = statement field exit)
    (initial : Signature u) (hnames : initial.sameName = contextNameProfile F c)
    (hselected : initial.selected = selected) (ambient : τ) (tapes : K → List Bool)
    (suffix : Position u → List Bool)
    (hfields : ∀ p, tapes (field p) =
      encodeWord (if positiveAt (PCP.clauseAt F (c p.1)) p.2 then 1 else 0) ++ suffix p) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some entryLabel, (initial, ambient), tapes⟩
      (some ⟨exit, (ofContext F c selected, ambient), tapes⟩) 1 := by
  have h := loadInTime field entryLabel exit program atEntry initial ambient tapes
    (ofContext F c selected).signs suffix hfields
  rw [loaded_ofContext F c selected initial hnames hselected] at h
  exact h


end DFVSGames.Foundations.Hastad.SourceSignLoad

end OAI
