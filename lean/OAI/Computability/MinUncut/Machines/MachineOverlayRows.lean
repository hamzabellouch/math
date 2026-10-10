import Mathlib
import OAI.Computability.MinUncut.Machines.MachineLazyRows
import OAI.Computability.MinUncut.PCP.PreprocessingOverlayWords

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineOverlayRows

open Turing MachineComposition
open PCP.GraphTables PCP.PreprocessingOverlayWords
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ A : Type} [DecidableEq K]
variable {e : Nat}

abbrev State (A : Type) (e : Nat) := MachinePortReindex.State A e

inductive Label (e : Nat)
  | loadStart | loadLoop | seedRelation
  | row (stage : MachineLazyRows.Label e)
  | drainOld | drainNew | drainRelation
  deriving DecidableEq, Fintype

def bodyIndex (i : Fin 9) : Fin 10 := i.castSucc

theorem bodyIndex_injective : Function.Injective bodyIndex := by
  intro i j h
  exact Fin.castSucc_injective 9 h

def trueBits : List Bool := encodeWords (relationWords trueRelation)

def instruction (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (labels : Label e → Λ) (exit : Option Λ) :
    Label e → TM2.Stmt (fun _ : K => Bool) Λ (State A e)
  | .loadStart => Hastad.SourceMachine.fieldStart (tape 1) (labels .loadLoop)
  | .loadLoop => Hastad.SourceMachine.fieldLoop (tape 9) (tape 1)
      (labels .loadLoop) (some (labels .seedRelation))
  | .seedRelation => pushWord (tape 2) trueBits.reverse
      (.goto fun _ => labels (.row (.inl .copySeed)))
  | .row stage => MachineLazyRows.reindexInstruction e positive (d + e) d
      (tape ∘ bodyIndex) (fun stage => labels (.row stage))
      (some (labels .drainOld)) stage
  | .drainOld => MachineDrain.drain (tape 1) (labels .drainOld) (some (labels .drainNew))
  | .drainNew => MachineDrain.drain (tape 6) (labels .drainNew) (some (labels .drainRelation))
  | .drainRelation => MachineDrain.drain (tape 2) (labels .drainRelation) exit

def rowBits (d e v j : Nat) : List Bool :=
  MachineLazyRows.reindexRowBits e (d + e) d v j trueRelation

def rowSteps (d e v j : Nat) (output : List Bool) : Nat :=
  (j + 2) + 1 + MachineLazyRows.reindexSteps e (d + e) d v j trueRelation output +
    (j + 2) + (MachinePortReindex.value e (d + e) d j + 2) + (trueBits.length + 1)

def resultTapes (d e v j : Nat) (tape : Fin 10 → K) (base : K → List Bool)
    (suffix : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 9) suffix) (tape 7)
    (base (tape 7) ++ rowBits d e v j)

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem rowTrace (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : Label e → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A e))
    (atLabels : ∀ l, program (labels l) = instruction d e positive tape labels exit l)
    (base : K → List Bool) (v j : Nat) (suffix : List Bool)
    (tailWord : base (tape 0) = encodeWord v)
    (inputWord : base (tape 9) = encodeWord j ++ suffix)
    (empty : ∀ i : Fin 10, i ≠ 0 → i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) :
    (advance (TM2.step program))^[rowSteps d e v j (base (tape 7))]
      (some ⟨some (labels .loadStart), MachinePortReindex.clean e positive ambient, base⟩) =
      some ⟨exit, MachinePortReindex.clean e positive ambient,
        resultTapes d e v j tape base suffix⟩ := by
  have hd (i k : Fin 10) (h : i ≠ k) : tape i ≠ tape k := fun x => h (distinct x)
  have h₁ := empty 1 (by decide) (by decide) (by decide)
  have h₂ := empty 2 (by decide) (by decide) (by decide)
  have h₃ := empty 3 (by decide) (by decide) (by decide)
  have h₄ := empty 4 (by decide) (by decide) (by decide)
  have h₅ := empty 5 (by decide) (by decide) (by decide)
  have h₆ := empty 6 (by decide) (by decide) (by decide)
  have h₈ := empty 8 (by decide) (by decide) (by decide)
  have hi0 : bodyIndex 0 = 0 := rfl
  have hi3 : bodyIndex 3 = 3 := rfl
  have hi4 : bodyIndex 4 = 4 := rfl
  have hi5 : bodyIndex 5 = 5 := rfl
  have hi6 : bodyIndex 6 = 6 := rfl
  have hi8 : bodyIndex 8 = 8 := rfl
  let loaded := Function.update (Function.update base (tape 9) suffix) (tape 1) (encodeWord j)
  let seeded := Function.update loaded (tape 2) trueBits
  let rowed := MachineLazyRows.reindexResultTapes e (d + e) d v j trueRelation
    (tape ∘ bodyIndex) seeded
  let oldCleared := Function.update rowed (tape 1) []
  let newCleared := Function.update oldCleared (tape 6) []
  have loadRun : (advance (TM2.step program))^[j + 2]
      (some ⟨some (labels .loadStart), MachinePortReindex.clean e positive ambient, base⟩) =
      some ⟨some (labels .seedRelation), MachinePortReindex.clean e positive ambient, loaded⟩ := by
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 1) (hd 9 1 (by decide))
      (labels .loadStart) (labels .loadLoop) (some (labels .seedRelation)) program
      (atLabels .loadStart) (atLabels .loadLoop) base j suffix inputWord
      (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
    change (advance (TM2.step program))^[j + 2]
      (some ⟨some (labels .loadStart), MachinePortReindex.clean e positive ambient, base⟩) =
      some ⟨some (labels .seedRelation), MachinePortReindex.clean e positive ambient,
        Hastad.SourceMachine.fieldTapes (tape 9) (tape 1) base suffix
          (encodeWord j ++ base (tape 1))⟩ at h
    simpa only [Hastad.SourceMachine.fieldTapes,
      h₁, List.append_nil, MachinePortReindex.clean, loaded] using h
  have seedRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .seedRelation), MachinePortReindex.clean e positive ambient, loaded⟩) =
      some ⟨some (labels (.row (.inl .copySeed))),
        MachinePortReindex.clean e positive ambient, seeded⟩ := by
    change some (TM2.stepAux (program (labels .seedRelation)) _ _) = _
    rw [atLabels]
    simp [instruction, stepAux_pushWord, TM2.stepAux, seeded, loaded,
      hd 2 1 (by decide), hd 2 9 (by decide), h₂]
  have hs (i : Fin 10) (hi : i ≠ 1) (hi' : i ≠ 2) (hi'' : i ≠ 9) :
      seeded (tape i) = base (tape i) := by
    simp [seeded, loaded, hd i 1 hi, hd i 2 hi', hd i 9 hi'']
  have bodyRun := MachineLazyRows.reindexRowTrace e positive (d + e) d
    (tape ∘ bodyIndex) (distinct.comp bodyIndex_injective) (fun s => labels (.row s))
    (some (labels .drainOld)) program (fun s => atLabels (.row s)) seeded v j trueRelation
    (by simpa only [Function.comp_apply, hi0] using
      (hs 0 (by decide) (by decide) (by decide)).trans tailWord)
    (by simp [seeded, loaded, Function.comp_apply, bodyIndex, hd 1 2 (by decide)])
    (by simp [seeded, Function.comp_apply, bodyIndex, trueBits])
    (by simpa only [Function.comp_apply, hi3] using
      (hs 3 (by decide) (by decide) (by decide)).trans h₃)
    (by simpa only [Function.comp_apply, hi4] using
      (hs 4 (by decide) (by decide) (by decide)).trans h₄)
    (by simpa only [Function.comp_apply, hi5] using
      (hs 5 (by decide) (by decide) (by decide)).trans h₅)
    (by simpa only [Function.comp_apply, hi6] using
      (hs 6 (by decide) (by decide) (by decide)).trans h₆)
    (by simpa only [Function.comp_apply, hi8] using
      (hs 8 (by decide) (by decide) (by decide)).trans h₈) ambient
  have hout : seeded ((tape ∘ bodyIndex) 7) = base (tape 7) :=
    hs 7 (by decide) (by decide) (by decide)
  rw [hout] at bodyRun
  change (advance (TM2.step program))^[MachineLazyRows.reindexSteps e (d + e) d v j
      trueRelation (base (tape 7))]
    (some ⟨some (labels (.row (.inl .copySeed))), MachinePortReindex.clean e positive ambient, seeded⟩) =
    some ⟨some (labels .drainOld), MachinePortReindex.clean e positive ambient, rowed⟩ at bodyRun
  have rowedOld : rowed (tape 1) = encodeWord j := by
    simp [rowed, MachineLazyRows.reindexResultTapes, MachineLazyRows.reindexMappedTapes,
      Function.comp_apply, bodyIndex, seeded, loaded, hd 1 7 (by decide),
      hd 1 6 (by decide), hd 1 2 (by decide)]
  have rowedNew : oldCleared (tape 6) = encodeWord (MachinePortReindex.value e (d + e) d j) := by
    simp [oldCleared, rowed, MachineLazyRows.reindexResultTapes,
      MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex,
      hd 6 1 (by decide), hd 6 7 (by decide)]
  have rowedRelation : newCleared (tape 2) = trueBits := by
    simp [newCleared, oldCleared, rowed, MachineLazyRows.reindexResultTapes,
      MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex, seeded,
      hd 2 6 (by decide), hd 2 1 (by decide), hd 2 7 (by decide)]
  have drainOld := (MachineDrain.drainInTime (tape 1) (labels .drainOld)
    (some (labels .drainNew)) program (atLabels .drainOld) rowed
    (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(rowed (tape 1)).length + 1]
    (some ⟨some (labels .drainOld), MachinePortReindex.clean e positive ambient, rowed⟩) =
    some ⟨some (labels .drainNew), MachinePortReindex.clean e positive ambient, oldCleared⟩ at drainOld
  rw [rowedOld, encodeWord_length] at drainOld
  have drainNew := (MachineDrain.drainInTime (tape 6) (labels .drainNew)
    (some (labels .drainRelation)) program (atLabels .drainNew) oldCleared
    (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(oldCleared (tape 6)).length + 1]
    (some ⟨some (labels .drainNew), MachinePortReindex.clean e positive ambient, oldCleared⟩) =
    some ⟨some (labels .drainRelation), MachinePortReindex.clean e positive ambient, newCleared⟩ at drainNew
  rw [rowedNew, encodeWord_length] at drainNew
  have drainRelation := (MachineDrain.drainInTime (tape 2) (labels .drainRelation)
    exit program (atLabels .drainRelation) newCleared
    (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(newCleared (tape 2)).length + 1]
    (some ⟨some (labels .drainRelation), MachinePortReindex.clean e positive ambient, newCleared⟩) =
    some ⟨exit, MachinePortReindex.clean e positive ambient,
      Function.update newCleared (tape 2) []⟩ at drainRelation
  rw [rowedRelation] at drainRelation
  have finalFrame : Function.update newCleared (tape 2) [] = resultTapes d e v j tape base suffix := by
    funext k
    by_cases h2 : k = tape 2
    · subst k
      simp [resultTapes, hd 2 7 (by decide), hd 2 9 (by decide), h₂]
    · by_cases h6 : k = tape 6
      · subst k
        simp [newCleared, resultTapes, hd 6 2 (by decide), hd 6 7 (by decide),
          hd 6 9 (by decide), h₆]
      · by_cases h1 : k = tape 1
        · subst k
          simp [newCleared, oldCleared, resultTapes, hd 1 2 (by decide),
            hd 1 6 (by decide), hd 1 7 (by decide), hd 1 9 (by decide), h₁]
        · by_cases h7 : k = tape 7
          · subst k
            simp [newCleared, oldCleared, rowed, MachineLazyRows.reindexResultTapes,
              MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex,
              resultTapes, rowBits, seeded, loaded, hd 7 2 (by decide),
              hd 7 6 (by decide), hd 7 1 (by decide), hd 7 9 (by decide)]
          · simp [newCleared, oldCleared, rowed, MachineLazyRows.reindexResultTapes,
              MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex,
              seeded, loaded, resultTapes, h2, h6, h1, h7]
  rw [finalFrame] at drainRelation
  exact joinTrace (joinTrace (joinTrace (joinTrace (joinTrace loadRun seedRun) bodyRun)
    drainOld) drainNew) drainRelation

theorem rowBits_eq_expanderRow {n : Nat} (d : Nat) (H : PCP.ExpanderTables.Table n e)
    (v : Fin n) (p : Fin e) :
    rowBits d e v.val (PCP.ExpanderTables.reverseIndex H
        (PCP.ExpanderTables.rowIndex n e (v, p))).val =
      encodeWords (rowWords (expanderRow d H v p)) := by
  rw [expanderRow_words]
  have h (j : Nat) : MachinePortReindex.value e (d + e) d j = expanderReverseMap d e j := by
    unfold MachinePortReindex.value expanderReverseMap
    omega
  simp only [rowBits, MachineLazyRows.reindexRowBits, h,
    PCP.PreprocessingLazyWords.relationWords_true, List.cons_append,
    List.nil_append, encodeWords, List.append_assoc]

def machine (d e : Nat) (positive : 0 < e) : FinTM2 where
  K := Fin 10
  k₀ := 9
  k₁ := 7
  Γ _ := Bool
  Λ := Label e
  main := .loadStart
  σ := State Unit e
  initialState := MachinePortReindex.clean e positive ()
  m := instruction d e positive id id none

abbrev VertexLabel (e : Nat) := Fin (e + 1) × Option (Label e)

def vertexInstruction (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (labels : VertexLabel e → Λ) (exit : Option Λ) :
    VertexLabel e → TM2.Stmt (fun _ : K => Bool) Λ (State A e)
  | (i, none) => if i.val < e then .goto fun _ => labels (i, some .loadStart)
      else MachinePortReindex.exitAt exit
  | (i, some stage) => if h : i.val < e then
      instruction d e positive tape (fun stage => labels (i, some stage))
        (some (labels (⟨i.val + 1, by omega⟩, none))) stage
      else MachinePortReindex.exitAt exit

def streamFrame (tape : Fin 10 → K) (base : K → List Bool)
    (words : List Nat) (output : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 9) (encodeWords words ++ base (tape 9)))
    (tape 7) output

def streamOutput (d e v : Nat) (words : List Nat) : List Bool :=
  words.flatMap (rowBits d e v)

def vertexSteps (d e v : Nat) : List Nat → List Bool → Nat
  | [], _ => 1
  | j :: words, output => 1 + rowSteps d e v j output +
      vertexSteps d e v words (output ++ rowBits d e v j)

def valueBound (d e B : Nat) : Nat := (d + e) * B + B + d
def rowSizeBound (d e v B : Nat) : Nat := v + valueBound d e B + trueBits.length + 2
def rowCostBound (d e v B : Nat) : Nat :=
  8 * B + 4 * rowSizeBound d e v B + valueBound d e B + trueBits.length + 28

theorem value_le (d e j B : Nat) (hj : j ≤ B) :
    MachinePortReindex.value e (d + e) d j ≤ valueBound d e B := by
  have hdiv := (Nat.div_le_self j e).trans hj
  have hmod := (Nat.mod_le j e).trans hj
  have hmul := Nat.mul_le_mul_left (d + e) hdiv
  unfold MachinePortReindex.value valueBound
  omega

theorem rowBits_length (d e v j : Nat) :
    (rowBits d e v j).length = v + MachinePortReindex.value e (d + e) d j + trueBits.length + 2 := by
  simp only [rowBits, MachineLazyRows.reindexRowBits, List.length_append, encodeWord_length,
    trueBits]
  omega

theorem rowBits_length_le (d e v j B : Nat) (hj : j ≤ B) :
    (rowBits d e v j).length ≤ rowSizeBound d e v B := by
  rw [rowBits_length]
  have h := value_le d e j B hj
  unfold rowSizeBound
  omega

theorem rowSteps_le (d e v j B : Nat) (hj : j ≤ B) (output : List Bool) :
    rowSteps d e v j output ≤ rowCostBound d e v B + 2 * output.length := by
  have hdiv := (Nat.div_le_self j e).trans hj
  have hval := value_le d e j B hj
  have hsize := rowBits_length_le d e v j B hj
  change (MachineLazyRows.reindexRowBits e (d + e) d v j trueRelation).length ≤
    rowSizeBound d e v B at hsize
  unfold rowSteps MachineLazyRows.reindexSteps MachinePortReindex.steps rowCostBound
  omega

private theorem vertexSteps_le_capacity (d e v B capacity : Nat)
    (words : List Nat) (bounded : ∀ j ∈ words, j ≤ B) (output : List Bool)
    (room : output.length + words.length * rowSizeBound d e v B ≤ capacity) :
    vertexSteps d e v words output ≤
      words.length * (rowCostBound d e v B + 2 * capacity + 1) + 1 := by
  induction words generalizing output with
  | nil => simp [vertexSteps]
  | cons j words ih =>
      have hj := bounded j (by simp)
      have hb : ∀ k ∈ words, k ≤ B := fun k hk => bounded k (by simp [hk])
      have hsize := rowBits_length_le d e v j B hj
      have hcost := rowSteps_le d e v j B hj output
      have hout : output.length ≤ capacity := by omega
      have hroom : (output ++ rowBits d e v j).length +
          words.length * rowSizeBound d e v B ≤ capacity := by
        rw [List.length_append]
        simp only [List.length_cons, Nat.succ_mul] at room
        omega
      have htail := ih hb (output ++ rowBits d e v j) hroom
      change 1 + rowSteps d e v j output +
        vertexSteps d e v words (output ++ rowBits d e v j) ≤
        (words.length + 1) * (rowCostBound d e v B + 2 * capacity + 1) + 1
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem vertexSteps_le (d e v B : Nat) (words : List Nat)
    (bounded : ∀ j ∈ words, j ≤ B) (output : List Bool) :
    vertexSteps d e v words output ≤
      words.length * (rowCostBound d e v B +
        2 * (output.length + words.length * rowSizeBound d e v B) + 1) + 1 :=
  vertexSteps_le_capacity d e v B _ words bounded output (Nat.le_refl _)

private theorem streamFrame_afterRow (d e v j : Nat) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (base : K → List Bool)
    (words : List Nat) (output : List Bool) :
    resultTapes d e v j tape (streamFrame tape base (j :: words) output)
      (encodeWords words ++ base (tape 9)) =
      streamFrame tape base words (output ++ rowBits d e v j) := by
  have h79 : tape 7 ≠ tape 9 := fun h => (by decide : (7 : Fin 10) ≠ 9) (distinct h)
  funext k
  by_cases h7 : k = tape 7
  · subst k
    simp [resultTapes, streamFrame]
  · by_cases h9 : k = tape 9
    · subst k
      simp [resultTapes, streamFrame, Ne.symm h79]
    · simp [resultTapes, streamFrame, h7, h9]

theorem vertexSuffixTrace (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : VertexLabel e → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A e))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d e positive tape labels exit l)
    (base : K → List Bool) (v : Nat) (values : Fin e → Nat)
    (tailWord : base (tape 0) = encodeWord v)
    (empty : ∀ i : Fin 10, i ≠ 0 → i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) (remaining : Nat) (i : Fin (e + 1)) (count : i.val + remaining = e)
    (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d e v ((List.ofFn values).drop i.val) output]
      (some ⟨some (labels (i, none)), MachinePortReindex.clean e positive ambient,
        streamFrame tape base ((List.ofFn values).drop i.val) output⟩) =
      some ⟨exit, MachinePortReindex.clean e positive ambient,
        streamFrame tape base [] (output ++ streamOutput d e v ((List.ofFn values).drop i.val))⟩ := by
  have hd (a b : Fin 10) (h : a ≠ b) : tape a ≠ tape b := fun x => h (distinct x)
  induction remaining generalizing i output with
  | zero =>
      have hi : i.val = e := by omega
      have hdrop : (List.ofFn values).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [List.length_ofFn, hi, le_refl]
      rw [hdrop]
      simp only [vertexSteps, streamOutput, List.flatMap_nil, List.append_nil]
      change some (TM2.stepAux (program (labels (i, none))) _ _) = _
      rw [atLabels]
      cases exit <;> simp [vertexInstruction, hi, MachinePortReindex.exitAt, TM2.stepAux]
  | succ remaining ih =>
      have hi : i.val < e := by omega
      let port : Fin e := ⟨i.val, hi⟩
      let next : Fin (e + 1) := ⟨i.val + 1, by omega⟩
      let rest := (List.ofFn values).drop (i.val + 1)
      have split : (List.ofFn values).drop i.val = values port :: rest := by
        have h := List.getElem_cons_drop (as := List.ofFn values)
          (i := i.val) (by simpa only [List.length_ofFn] using hi)
        simpa only [List.getElem_ofFn, port, rest] using h.symm
      let initial := streamFrame tape base (values port :: rest) output
      have boundary : (advance (TM2.step program))^[1]
          (some ⟨some (labels (i, none)), MachinePortReindex.clean e positive ambient, initial⟩) =
          some ⟨some (labels (i, some .loadStart)), MachinePortReindex.clean e positive ambient, initial⟩ := by
        change some (TM2.stepAux (program (labels (i, none))) _ _) = _
        rw [atLabels]
        simp [vertexInstruction, hi, TM2.stepAux]
      have body := rowTrace d e positive tape distinct (fun stage => labels (i, some stage))
        (some (labels (next, none))) program
        (by
          intro stage
          simpa only [vertexInstruction, hi, dite_true, next] using
            (atLabels (i, some stage))) initial v (values port)
        (encodeWords rest ++ base (tape 9))
        (by simp [initial, streamFrame, hd 0 7 (by decide), hd 0 9 (by decide), tailWord])
        (by simp [initial, streamFrame, hd 9 7 (by decide), encodeWords, List.append_assoc])
        (by
          intro k hk0 hk7 hk9
          simp [initial, streamFrame, hd k 7 hk7, hd k 9 hk9, empty k hk0 hk7 hk9]) ambient
      have initialOutput : initial (tape 7) = output := by simp [initial, streamFrame]
      rw [initialOutput] at body
      change (advance (TM2.step program))^[rowSteps d e v (values port) output]
        (some ⟨some (labels (i, some .loadStart)), MachinePortReindex.clean e positive ambient, initial⟩) =
        some ⟨some (labels (next, none)), MachinePortReindex.clean e positive ambient,
          resultTapes d e v (values port) tape initial (encodeWords rest ++ base (tape 9))⟩ at body
      rw [show resultTapes d e v (values port) tape initial (encodeWords rest ++ base (tape 9)) =
        streamFrame tape base rest (output ++ rowBits d e v (values port)) from
          streamFrame_afterRow d e v (values port) tape distinct base rest output] at body
      have nextCount : next.val + remaining = e := by dsimp [next]; omega
      have tail := ih next nextCount (output ++ rowBits d e v (values port))
      change (advance (TM2.step program))^[vertexSteps d e v rest (output ++ rowBits d e v (values port))]
        (some ⟨some (labels (next, none)), MachinePortReindex.clean e positive ambient,
          streamFrame tape base rest (output ++ rowBits d e v (values port))⟩) =
        some ⟨exit, MachinePortReindex.clean e positive ambient,
          streamFrame tape base [] ((output ++ rowBits d e v (values port)) ++ streamOutput d e v rest)⟩ at tail
      rw [split]
      have all := joinTrace (joinTrace boundary body) tail
      simpa only [vertexSteps, initial, streamOutput, List.flatMap_cons, List.append_assoc] using all

theorem vertexTrace (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : VertexLabel e → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A e))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d e positive tape labels exit l)
    (base : K → List Bool) (v : Nat) (values : Fin e → Nat)
    (tailWord : base (tape 0) = encodeWord v)
    (empty : ∀ i : Fin 10, i ≠ 0 → i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d e v (List.ofFn values) output]
      (some ⟨some (labels (0, none)), MachinePortReindex.clean e positive ambient,
        streamFrame tape base (List.ofFn values) output⟩) =
      some ⟨exit, MachinePortReindex.clean e positive ambient,
        streamFrame tape base [] (output ++ streamOutput d e v (List.ofFn values))⟩ := by
  simpa only [Fin.val_zero, List.drop_zero] using vertexSuffixTrace d e positive tape distinct
    labels exit program atLabels base v values tailWord empty ambient e 0 (by simp) output

def vertexInTime (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : VertexLabel e → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A e))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d e positive tape labels exit l)
    (base : K → List Bool) (v B : Nat) (values : Fin e → Nat)
    (bounded : ∀ p, values p ≤ B)
    (tailWord : base (tape 0) = encodeWord v)
    (empty : ∀ i : Fin 10, i ≠ 0 → i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) (output : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (0, none)), MachinePortReindex.clean e positive ambient,
        streamFrame tape base (List.ofFn values) output⟩
      (some ⟨exit, MachinePortReindex.clean e positive ambient,
        streamFrame tape base [] (output ++ streamOutput d e v (List.ofFn values))⟩)
      (e * (rowCostBound d e v B + 2 * (output.length + e * rowSizeBound d e v B) + 1) + 1) where
  steps := vertexSteps d e v (List.ofFn values) output
  evals_in_steps := vertexTrace d e positive tape distinct labels exit program atLabels
    base v values tailWord empty ambient output
  steps_le_m := by
    simpa only [List.length_ofFn] using vertexSteps_le d e v B (List.ofFn values)
      (by intro j hj; obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hj; exact bounded p) output

theorem encodeWords_flatMap {α : Type*} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun x => encodeWords (words x)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem streamOutput_expanderRows {n : Nat} (d : Nat) (H : PCP.ExpanderTables.Table n e)
    (v : Fin n) :
    streamOutput d e v.val (List.ofFn fun p : Fin e =>
      (PCP.ExpanderTables.reverseIndex H (PCP.ExpanderTables.rowIndex n e (v, p))).val) =
      encodeWords ((List.ofFn (expanderRow d H v)).flatMap rowWords) := by
  rw [encodeWords_flatMap]
  simp only [streamOutput, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  exact rowBits_eq_expanderRow d H v p

theorem expanderValues_bounded {n : Nat} (H : PCP.ExpanderTables.Table n e) (v : Fin n)
    (p : Fin e) :
    (PCP.ExpanderTables.reverseIndex H (PCP.ExpanderTables.rowIndex n e (v, p))).val ≤ n * e :=
  (PCP.ExpanderTables.reverseIndex H (PCP.ExpanderTables.rowIndex n e (v, p))).isLt.le

def vertexMachine (d e : Nat) (positive : 0 < e) : FinTM2 where
  K := Fin 10
  k₀ := 9
  k₁ := 7
  Γ _ := Bool
  Λ := VertexLabel e
  main := (0, none)
  σ := State Unit e
  initialState := MachinePortReindex.clean e positive ()
  m := vertexInstruction d e positive id id none

end MinUncutGames.Foundations.Complexity.MachineOverlayRows

end

end OAI
