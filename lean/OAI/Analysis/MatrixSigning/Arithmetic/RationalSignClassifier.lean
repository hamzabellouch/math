import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalCompareDeterministic
import OAI.Analysis.MatrixSigning.Machines.CleanupDeterministic

namespace OAI

section

namespace KS.W06.RationalSignClassifier

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare
open KS.W04.CleanRationalCompare

def outputCode (q : ℚ) : List Bool :=
  if q < 0 then [false] else if q = 0 then [true] else []

def rawCode (sign : Bool) (num : List Bool) : List Bool :=
  if sign then [false] else if num = [] then [true] else []

def classifyDispatch (_ : Fin 1) (heads : Fin 13 → Fin 3) (_ : Bool) : Instruction 13 1 :=
  ⟨none, Vector.ofFn (fun j => if j = 9 then
    if heads 12 = 2 then .push false else if heads 10 = 0 then .push true else .stay
    else .stay)⟩

def classifyProgram : Program 13 :=
  ofMachine (compile (0 : Fin 1) 0 9 classifyDispatch)

def classifiedState (before : Fin 13 → List Bool) (sign : Bool) (num : List Bool) :
    Fin 13 → List Bool := fun j => if j = 9 then rawCode sign num else before j

theorem classify_spec (before : Fin 13 → List Bool) (sign : Bool) (num : List Bool)
    (hs : before 12 = [sign]) (hn : before 10 = num) (ho : before 9 = []) :
    RunSpec classifyProgram before (classifiedState before sign num) 1 := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
    (compile (0 : Fin 1) (0 : Fin 13) (9 : Fin 13) classifyDispatch)
  intro bits hlen
  obtain ⟨coin, rfl⟩ := List.length_eq_one_iff.mp hlen
  change (compile (0 : Fin 1) (0 : Fin 13) (9 : Fin 13) classifyDispatch).step
    ⟨some (0 : Fin 1), before⟩ coin = _
  erw [step_compile]
  apply congrArg (Config.mk none)
  funext j
  by_cases hj : j = 9
  · subst j
    cases sign <;> cases num <;>
      simp [classifyDispatch, Instruction.action, classifiedState, rawCode,
        observedHeads, KS.W29.topCode, KS.W29.StackAction.apply, hs, hn, ho]
    all_goals
      rename_i head tail
      cases head <;> rfl
  · simp [classifyDispatch, Instruction.action, classifiedState, hj,
      KS.W29.StackAction.apply]

theorem encodeNat_eq_nil (n : ℕ) : Computability.encodeNat n = [] ↔ n = 0 := by
  constructor
  · intro h
    have hv := congrArg KS.W19.bitsValue h
    simpa only [KS.W19.bitsValue_encodeNat, KS.W19.bitsValue] using hv
  · rintro rfl
    rfl

theorem rawCode_canonical (q : ℚ) :
    rawCode (decide (q.num < 0)) (Computability.encodeNat q.num.natAbs) = outputCode q := by
  have hs : q.num < 0 ↔ q < 0 := by
    simpa only [not_le] using not_congr
      (show 0 ≤ q.num ↔ 0 ≤ q from Rat.num_nonneg)
  have hz : Computability.encodeNat q.num.natAbs = [] ↔ q = 0 := by
    rw [encodeNat_eq_nil, Int.natAbs_eq_zero, Rat.num_eq_zero]
  simp [rawCode, outputCode, hs, hz]

def parsedState (q : ℚ) : Fin 13 → List Bool := SingleRationalParser.canonicalState q

def classifiedCanonical (q : ℚ) : Fin 13 → List Bool :=
  classifiedState (parsedState q) (decide (q.num < 0)) (Computability.encodeNat q.num.natAbs)

def outputState (q : ℚ) : Fin 13 → List Bool := fun j => if j = 9 then outputCode q else []

def readProgram : Program 13 := compose SingleRationalParser.program classifyProgram

def readTicks (q : ℚ) : ℕ := 8 * (KS.W01.ratLength q + 1) + 1

theorem read_spec (q : ℚ) :
    RunSpec readProgram (SingleRationalParser.inputState (KS.W01.encodeRat q))
      (classifiedCanonical q) (readTicks q) := by
  have hp := SingleRationalParser.canonical_spec q []
  simp only [List.append_nil] at hp
  exact hp.compose (classify_spec (parsedState q) _ _ rfl rfl rfl)

theorem classified_length (q : ℚ) (j : Fin 13) :
    (classifiedCanonical q j).length ≤ KS.W01.ratLength q + readTicks q := by
  let bits := List.replicate (readTicks q) false
  have hr := read_spec q bits (by simp [bits])
  have hg := readProgram.toMachine.run_stack_length_le
    ⟨some readProgram.initial, SingleRationalParser.inputState (KS.W01.encodeRat q)⟩ bits j
  rw [hr] at hg
  have hi : (SingleRationalParser.inputState (KS.W01.encodeRat q) j).length ≤ KS.W01.ratLength q := by
    fin_cases j <;> simp [SingleRationalParser.inputState, KS.W01.ratLength]
  simpa only [bits, List.length_replicate] using hg.trans (Nat.add_le_add_right hi _)

theorem cleared_classified (q : ℚ) :
    clearListState scratchPorts (classifiedCanonical q) = outputState q := by
  funext j
  rw [clearListState_apply]
  fin_cases j <;> simp [scratchPorts, outputState, classifiedCanonical, classifiedState]
  simpa using rawCode_canonical q

def program : Program 13 := compose readProgram cleanupProgram

theorem canonical_spec (q : ℚ) :
    RunSpec program (SingleRationalParser.inputState (KS.W01.encodeRat q)) (outputState q)
      (256 * (KS.W01.ratLength q + 1)) := by
  have h := (read_spec q).compose (clearList_spec 9 scratchPorts (classifiedCanonical q))
  rw [cleared_classified] at h
  apply h.mono
  have hb := clearListTicks_le scratchPorts (classifiedCanonical q)
    (KS.W01.ratLength q + readTicks q) (classified_length q)
  change clearListTicks scratchPorts (classifiedCanonical q) ≤
    12 * (KS.W01.ratLength q + readTicks q + 1) + 1 at hb
  unfold readTicks at hb ⊢
  omega

def onPorts {k : ℕ} (ports : Fin 13 ↪ Fin k) : Program k := liftPorts program ports

theorem onPorts_spec {k : ℕ} (ports : Fin 13 ↪ Fin k) (before : Fin k → List Bool)
    (q : ℚ) (hbefore : (fun i => before (ports i)) =
      SingleRationalParser.inputState (KS.W01.encodeRat q)) :
    RunSpec (onPorts ports) before (replacePorts ports before (outputState q))
      (256 * (KS.W01.ratLength q + 1)) := by
  apply runSpec_liftPorts
  rw [hbefore]
  exact canonical_spec q

theorem coinIndependent : KS.W29.Deterministic.CoinIndependent program :=
  KS.W29.Deterministic.coinIndependent_compose _ _
    (KS.W29.Deterministic.coinIndependent_compose _ _
      RationalCompareDeterministic.single_coinIndependent
      (KS.W29.Deterministic.coinIndependent_compile (0 : Fin 1) 0 9 classifyDispatch
        (fun _ _ _ _ => rfl))) cleanup_coinIndependent

@[simp] theorem program_output : program.output = 9 := rfl

end KS.W06.RationalSignClassifier

end

end OAI
