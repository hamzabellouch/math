import OAI.Computability.PerfectCompleteness.Machines.BinaryNameCompare

namespace OAI


namespace PerfectCompleteness.CanonicalDictionaryAppendMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := BinaryNameCompare.State A
abbrev clean (ambient : A) : State A := BinaryNameCompare.clean ambient

def payload (bits : List Bool) : List Bool := bits.flatMap fun bit => [true, bit]

theorem payload_frame (bits : List Bool) :
    payload bits ++ [false] = BinaryNameMachine.frame bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      simpa [payload, BinaryNameMachine.frame] using congrArg (fun tail => true :: bit :: tail) ih

def finish (destination : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1) (exitAt destination exit)

def emitLoop (source destination : K) (again : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push destination (fun state => state.2.getD false)
        (.push destination (fun _ => true) (finish destination (some again))))
      (.push destination (fun _ => false) (finish destination exit)))

private theorem update_source (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) source replacement =
      tapesAt source destination base replacement output := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapesAt, distinct]
  · by_cases hd : k = destination
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

private theorem update_destination (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) destination replacement =
      tapesAt source destination base input replacement := by
  simp [tapesAt]

theorem emitStep_empty (source destination : K) (distinct : source ≠ destination)
    (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLoop : program again = emitLoop source destination again exit)
    (base : K → List Bool) (output : List Bool) (ambient : A) :
    TM2.step program
      ⟨some again, clean ambient, tapesAt source destination base [] output⟩ =
      some ⟨exit, clean ambient, tapesAt source destination base [] (false :: output)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atLoop]
  cases exit <;>
    simp [emitLoop, finish, exitAt, TM2.stepAux, clean, BinaryNameCompare.clean,
      distinct, update_source, update_destination]

theorem emitStep_cons (source destination : K) (distinct : source ≠ destination)
    (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLoop : program again = emitLoop source destination again exit)
    (base : K → List Bool) (bit : Bool) (input output : List Bool) (ambient : A) :
    TM2.step program
      ⟨some again, clean ambient, tapesAt source destination base (bit :: input) output⟩ =
      some ⟨some again, clean ambient,
        tapesAt source destination base input (true :: bit :: output)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atLoop]
  simp [emitLoop, finish, exitAt, TM2.stepAux, clean, BinaryNameCompare.clean,
    distinct, update_source, update_destination]

theorem emitTrace (source destination : K) (distinct : source ≠ destination)
    (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLoop : program again = emitLoop source destination again exit)
    (base : K → List Bool) (input output : List Bool) (ambient : A) :
    (advance (TM2.step program))^[input.length + 1]
      (some ⟨some again, clean ambient, tapesAt source destination base input output⟩) =
      some ⟨exit, clean ambient,
        tapesAt source destination base [] (false :: (payload input.reverse ++ output))⟩ := by
  induction input generalizing output with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
        List.reverse_nil, payload, List.flatMap_nil, List.nil_append] using
        emitStep_empty source destination distinct again exit program atLoop base output ambient
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [emitStep_cons source destination distinct again exit program atLoop, ih]
      simp only [List.reverse_cons, payload, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc, List.cons_append,
        List.nil_append]

inductive Label
  | copyOut | copyBack | save | seed | emit | restore
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyOut, .copyBack, .save, .seed, .emit,
  .restore]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def instruction (tape : Fin 5 → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .copyOut => loopAt (tape 0) (tape 3) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (tape 3) (tape 0) (tape 2) false
      (labels .copyBack) (some (labels .save))
  | .save => loopAt (tape 1) (tape 4) id false
      (labels .save) (some (labels .seed))
  | .seed => .push (tape 1) (fun _ => false) (.goto fun _ => labels .emit)
  | .emit => emitLoop (tape 2) (tape 1) (labels .emit) (some (labels .restore))
  | .restore => loopAt (tape 4) (tape 1) id false (labels .restore) exit

def steps (keyLength dictionaryLength : Nat) : Nat :=
  3 * keyLength + 2 * dictionaryLength + 6

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem appendTrace (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels exit l)
    (base : K → List Bool) (bits dictionary : List Bool)
    (keyWord : base (tape 0) = bits.reverse)
    (dictionaryWord : base (tape 1) = dictionary)
    (copyEmpty : base (tape 2) = []) (scratchEmpty : base (tape 3) = [])
    (savedEmpty : base (tape 4) = []) (ambient : A) :
    (advance (TM2.step program))^[steps bits.length dictionary.length]
      (some ⟨some (labels .copyOut), clean ambient, base⟩) =
      some ⟨exit, clean ambient,
        Function.update base (tape 1) (dictionary ++ (false :: BinaryNameMachine.frame bits))⟩ := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  let copyBase := Function.update base (tape 2) bits.reverse
  let savedBase := tapesAt (tape 1) (tape 4) copyBase [] dictionary.reverse
  let seedBase := Function.update savedBase (tape 1) [false]
  let emittedBase := tapesAt (tape 2) (tape 1) seedBase []
    (false :: BinaryNameMachine.frame bits)
  have copyRun : (advance (TM2.step program))^[2 * (bits.length + 1)]
      (some ⟨some (labels .copyOut), clean ambient, base⟩) =
      some ⟨some (labels .save), clean ambient, copyBase⟩ := by
    have h := MachineCopy.copyTrace (tape 0) (tape 2) (tape 3)
      (hd 0 2 (by decide)) (hd 0 3 (by decide)) (hd 2 3 (by decide)) false
      (labels .copyOut) (labels .copyBack) (some (labels .save)) program
      (atLabels .copyOut) (atLabels .copyBack) base scratchEmpty
      (ambient, false, none) none
    simpa only [keyWord, copyEmpty, List.append_nil, List.length_reverse,
      clean, BinaryNameCompare.clean, copyBase] using h
  have copyDictionary : copyBase (tape 1) = dictionary := by
    simpa [copyBase, hd 1 2 (by decide)] using dictionaryWord
  have copySaved : copyBase (tape 4) = [] := by
    simpa [copyBase, hd 4 2 (by decide)] using savedEmpty
  have saveRun : (advance (TM2.step program))^[dictionary.length + 1]
      (some ⟨some (labels .save), clean ambient, copyBase⟩) =
      some ⟨some (labels .seed), clean ambient, savedBase⟩ := by
    have h := transferAt_fromTapes (Γ := Alphabet) (σ := A × Bool × Option Bool)
      (tape 1) (tape 4) (hd 1 4 (by decide)) id false (labels .save)
      (some (labels .seed)) program (atLabels .save) copyBase (ambient, false, none) none
    change (advance (TM2.step program))^[(copyBase (tape 1)).length + 1]
      (some ⟨some (labels .save), clean ambient, copyBase⟩) =
      some ⟨some (labels .seed), clean ambient, tapesAt (tape 1) (tape 4) copyBase []
        ((copyBase (tape 1)).reverse.map id ++ copyBase (tape 4))⟩ at h
    simpa only [copyDictionary, copySaved, List.map_id,
      List.append_nil, clean, BinaryNameCompare.clean, savedBase] using h
  have seedRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .seed), clean ambient, savedBase⟩) =
      some ⟨some (labels .emit), clean ambient, seedBase⟩ := by
    simp only [Function.iterate_one, advance_some]
    change some (TM2.stepAux (program (labels .seed)) _ _) = _
    rw [atLabels .seed]
    simp [instruction, TM2.stepAux, savedBase, tapesAt, seedBase, hd 1 4 (by decide)]
  have seedKey : seedBase (tape 2) = bits.reverse := by
    simp [seedBase, savedBase, tapesAt, copyBase, hd 2 1 (by decide), hd 2 4 (by decide)]
  have seedDictionary : seedBase (tape 1) = [false] := by simp [seedBase]
  have emitRun : (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some (labels .emit), clean ambient, seedBase⟩) =
      some ⟨some (labels .restore), clean ambient, emittedBase⟩ := by
    have h := emitTrace (tape 2) (tape 1) (hd 2 1 (by decide))
      (labels .emit) (some (labels .restore)) program (atLabels .emit) seedBase
      (seedBase (tape 2)) (seedBase (tape 1)) ambient
    rw [tapesAt_self] at h
    simpa only [seedKey, seedDictionary, List.length_reverse, List.reverse_reverse,
      payload_frame, emittedBase] using h
  have emittedSaved : emittedBase (tape 4) = dictionary.reverse := by
    simp [emittedBase, seedBase, savedBase, tapesAt,
      hd 4 1 (by decide), hd 4 2 (by decide)]
  have emittedDictionary : emittedBase (tape 1) =
      false :: BinaryNameMachine.frame bits := by simp [emittedBase]
  have restored : tapesAt (tape 4) (tape 1) emittedBase []
      (dictionary ++ (false :: BinaryNameMachine.frame bits)) =
      Function.update base (tape 1) (dictionary ++ (false :: BinaryNameMachine.frame bits)) := by
    funext k
    by_cases h1 : k = tape 1
    · subst k; simp [tapesAt]
    · by_cases h2 : k = tape 2
      · subst k
        simp [tapesAt, emittedBase, hd 2 1 (by decide), hd 2 4 (by decide), copyEmpty]
      · by_cases h4 : k = tape 4
        · subst k
          simp [tapesAt, hd 4 1 (by decide), savedEmpty]
        · simp [tapesAt, emittedBase, seedBase, savedBase, copyBase, h1, h2, h4]
  have restoreRun : (advance (TM2.step program))^[dictionary.length + 1]
      (some ⟨some (labels .restore), clean ambient, emittedBase⟩) =
      some ⟨exit, clean ambient,
        Function.update base (tape 1) (dictionary ++ (false :: BinaryNameMachine.frame bits))⟩ := by
    have h := transferAt_fromTapes (Γ := Alphabet) (σ := A × Bool × Option Bool)
      (tape 4) (tape 1) (hd 4 1 (by decide)) id false (labels .restore) exit
      program (atLabels .restore) emittedBase (ambient, false, none) none
    change (advance (TM2.step program))^[(emittedBase (tape 4)).length + 1]
      (some ⟨some (labels .restore), clean ambient, emittedBase⟩) =
      some ⟨exit, clean ambient, tapesAt (tape 4) (tape 1) emittedBase []
        ((emittedBase (tape 4)).reverse.map id ++ emittedBase (tape 1))⟩ at h
    simpa only [emittedSaved, emittedDictionary, List.length_reverse,
      List.reverse_reverse, List.map_id, restored, clean, BinaryNameCompare.clean] using h
  have h := joinTrace (joinTrace (joinTrace (joinTrace copyRun saveRun) seedRun) emitRun) restoreRun
  have time : (((2 * (bits.length + 1) + (dictionary.length + 1)) + 1) +
      (bits.length + 1)) + (dictionary.length + 1) = steps bits.length dictionary.length := by
    unfold steps
    omega
  rw [time] at h
  exact h

def appendInTime (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels exit l)
    (base : K → List Bool) (bits dictionary : List Bool)
    (keyWord : base (tape 0) = bits.reverse)
    (dictionaryWord : base (tape 1) = dictionary)
    (copyEmpty : base (tape 2) = []) (scratchEmpty : base (tape 3) = [])
    (savedEmpty : base (tape 4) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copyOut), clean ambient, base⟩
      (some ⟨exit, clean ambient,
        Function.update base (tape 1) (dictionary ++ (false :: BinaryNameMachine.frame bits))⟩)
      (3 * bits.length + 2 * dictionary.length + 6) where
  steps := steps bits.length dictionary.length
  evals_in_steps := appendTrace tape distinct labels exit program atLabels base bits dictionary
    keyWord dictionaryWord copyEmpty scratchEmpty savedEmpty ambient
  steps_le_m := Nat.le_refl _

def machine : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Label
  main := .copyOut
  σ := State Unit
  initialState := clean ()
  m := instruction id id none

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end PerfectCompleteness.CanonicalDictionaryAppendMachine

end OAI
