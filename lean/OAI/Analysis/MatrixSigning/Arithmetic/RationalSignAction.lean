import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.SignedRationalSerializer
import OAI.Analysis.MatrixSigning.Arithmetic.SingleRationalParser

namespace OAI

namespace KS.W16.RationalSignAction
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def signedRational (eps : Bool) (q : ℚ) : ℚ := if eps then q else -q

def extend (r : Fin 13 → List Bool) (tape : List Bool) : Fin 14 → List Bool :=
  fun j => if h : j.val < 13 then r ⟨j.val,h⟩ else tape

def corePorts : Fin 13 ↪ Fin 14 := Fin.castLEEmb (by decide)
def inputState (wire tape : List Bool) : Fin 14 → List Bool :=
  extend (KS.W06.SingleRationalParser.inputState wire) tape
def operandState (num den : List Bool) (sgn : Bool) (tape : List Bool) : Fin 14 → List Bool :=
  extend (KS.W01.SignedRationalSerializer.inputState num den sgn) tape
def poppedState (num den tape : List Bool) : Fin 14 → List Bool :=
  ![[],[],[],[],[],[],[],[],[],[],num,den,[],tape]
def outputState (wire tape : List Bool) : Fin 14 → List Bool :=
  extend (KS.W01.SignedRationalSerializer.outputState wire) tape

def chooseSign (num : List Bool) (sgn eps : Bool) : Bool :=
  if num = [] then false else if eps then sgn else !sgn

def headSign (heads : Fin 14 → Fin 3) : Bool :=
  if (heads 10).val = 0 then false else
    if (heads 13).val = 2 then (heads 12).val == 2 else !((heads 12).val == 2)

def toggleDispatch (s : Fin 3) (heads : Fin 14 → Fin 3) (_ : Bool) : Instruction 14 3 :=
  if s.val = 0 then
    ⟨some (if headSign heads then 2 else 1),
      Vector.ofFn (fun j => if j = 12 then .pop else .stay)⟩
  else ⟨none, Vector.ofFn (fun j => if j = 12 then .push (s.val == 2) else .stay)⟩

def toggleMachine : Machine := compile (0 : Fin 3) (0 : Fin 14) (12 : Fin 14) toggleDispatch
def toggleProgram : Program 14 := ofMachine toggleMachine

theorem toggle_step_start (num den : List Bool) (sgn eps : Bool) (tail : List Bool) (coin : Bool) :
    toggleMachine.step ⟨some (0 : Fin 3), operandState num den sgn (eps :: tail)⟩ coin =
      ⟨some (if chooseSign num sgn eps then (2 : Fin 3) else (1 : Fin 3)), poppedState num den (eps :: tail)⟩ := by
  unfold toggleMachine
  rw [step_compile]
  cases num with
  | nil =>
    cases sgn <;> cases eps <;>
      apply congrArg₂ Config.mk
    all_goals first | (solve | rfl) |
      (funext j; fin_cases j <;> rfl)
  | cons b bs =>
    cases b <;> cases sgn <;> cases eps <;>
      apply congrArg₂ Config.mk
    all_goals first | (solve | rfl) |
      (funext j; fin_cases j <;> rfl)

theorem toggle_step_finish (num den tape : List Bool) (sgn : Bool) (coin : Bool) :
    toggleMachine.step ⟨some (if sgn then (2 : Fin 3) else (1 : Fin 3)), poppedState num den tape⟩ coin =
      ⟨none, operandState num den sgn tape⟩ := by
  unfold toggleMachine
  cases sgn <;> erw [step_compile]
  all_goals
    apply congrArg₂ Config.mk
    · rfl
    · funext j; fin_cases j <;> rfl

theorem toggle_spec (num den : List Bool) (sgn eps : Bool) (tail : List Bool) :
    RunSpec toggleProgram (operandState num den sgn (eps :: tail))
      (operandState num den (chooseSign num sgn eps) (eps :: tail)) 2 := by
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine toggleMachine
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons b bs =>
    cases bs with
    | nil => simp at hbits
    | cons c cs =>
      have he : cs = [] := by apply List.length_eq_zero_iff.mp; simpa using hbits
      subst cs
      change toggleMachine.run ⟨some (0 : Fin 3), operandState num den sgn (eps :: tail)⟩ [b,c] = _
      rw [Machine.run, toggle_step_start, Machine.run, toggle_step_finish]
      rfl

theorem encoded_nat_eq_nil (n : ℕ) : Computability.encodeNat n = [] ↔ n = 0 := by
  constructor
  · intro h
    have hv := congrArg KS.W19.bitsValue h
    simpa only [KS.W19.bitsValue_encodeNat, KS.W19.bitsValue] using hv
  · rintro rfl
    rfl

theorem chooseSign_integer (z : ℤ) (eps : Bool) :
    chooseSign (Computability.encodeNat z.natAbs) (decide (z < 0)) eps =
      decide ((if eps then z else -z) < 0) := by
  by_cases hz : z = 0
  · subst z
    cases eps <;> simp [chooseSign, encoded_nat_eq_nil]
  · have hn : z.natAbs ≠ 0 := by simpa using hz
    by_cases hneg : z < 0
    · cases eps <;> simp [chooseSign, encoded_nat_eq_nil, hn, hneg]
      omega
    · cases eps <;> simp [chooseSign, encoded_nat_eq_nil, hn, hneg]
      omega

@[simp] theorem signedRational_num_abs (eps : Bool) (q : ℚ) :
    (signedRational eps q).num.natAbs = q.num.natAbs := by
  cases eps <;> simp [signedRational]
@[simp] theorem signedRational_den (eps : Bool) (q : ℚ) :
    (signedRational eps q).den = q.den := by
  cases eps <;> simp [signedRational]
theorem chooseSign_rational (q : ℚ) (eps : Bool) :
    chooseSign (Computability.encodeNat q.num.natAbs) (decide (q.num < 0)) eps =
      decide ((signedRational eps q).num < 0) := by
  have h := chooseSign_integer q.num eps
  cases eps <;> simpa [signedRational] using h

def parseProgram : Program 14 :=
  KS.W29.FixedSequential.liftPorts KS.W06.SingleRationalParser.program corePorts
def serializeProgram : Program 14 :=
  KS.W29.FixedSequential.liftPorts KS.W01.SignedRationalSerializer.program corePorts
def program : Program 14 := compose (compose parseProgram toggleProgram) serializeProgram
def machine : Machine := program.toMachine

private theorem extend_on (r : Fin 13 → List Bool) (tape : List Bool) (i : Fin 13) :
    extend r tape (corePorts i) = r i := by
  change dite (i.val < 13) (fun h => r ⟨i.val,h⟩) _ = r i
  exact dite_eq_left i.isLt

private theorem extend_off (r : Fin 13 → List Bool) (tape : List Bool) (j : Fin 14)
    (hj : ∀ i, j ≠ corePorts i) : extend r tape j = tape := by
  have hnot : ¬ j.val < 13 := by
    intro h
    exact hj ⟨j.val,h⟩ (Fin.ext rfl)
  simp only [extend, hnot, dite_false]

theorem liftCore_spec (P : Program 13) (before result : Fin 13 → List Bool)
    (tape : List Bool) (cost : ℕ) (h : RunSpec P before result cost) :
    RunSpec (KS.W29.FixedSequential.liftPorts P corePorts)
      (extend before tape) (extend result tape) cost :=
  KS.W01.FixedPortRunSpec.lift_runSpec P corePorts before result
    (extend before tape) (extend result tape) cost h
    (extend_on before tape) (extend_on result tape)
    (fun j hj => (extend_off result tape j hj).trans (extend_off before tape j hj).symm)

theorem parse_spec (q : ℚ) (tape : List Bool) :
    RunSpec parseProgram (inputState (KS.W01.encodeRat q) tape)
      (operandState (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den)
        (decide (q.num < 0)) tape) (8 * (KS.W01.ratLength q + 1)) := by
  have h := KS.W06.SingleRationalParser.canonical_spec q []
  simp only [List.append_nil] at h
  exact liftCore_spec KS.W06.SingleRationalParser.program _ _ tape _ h

theorem serialize_spec (q : ℚ) (tape : List Bool) :
    RunSpec serializeProgram
      (operandState (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den)
        (decide (q.num < 0)) tape)
      (outputState (KS.W01.encodeRat q) tape)
      (16 * ((Computability.encodeNat q.num.natAbs).length +
        (Computability.encodeNat q.den).length + 1)) :=
  liftCore_spec KS.W01.SignedRationalSerializer.program _ _ tape _
    (KS.W01.SignedRationalSerializer.serializes_rational q)

def ticks (q : ℚ) : ℕ := 8 * (KS.W01.ratLength q + 1) + 2 +
  16 * ((Computability.encodeNat q.num.natAbs).length + (Computability.encodeNat q.den).length + 1)

theorem full_spec (q : ℚ) (eps : Bool) (tail : List Bool) :
    RunSpec program (inputState (KS.W01.encodeRat q) (eps :: tail))
      (outputState (KS.W01.encodeRat (signedRational eps q)) (eps :: tail)) (ticks q) := by
  have ht := toggle_spec (Computability.encodeNat q.num.natAbs)
    (Computability.encodeNat q.den) (decide (q.num < 0)) eps tail
  rw [chooseSign_rational] at ht
  have hs := serialize_spec (signedRational eps q) (eps :: tail)
  simp only [signedRational_num_abs, signedRational_den] at hs
  exact ((parse_spec q (eps :: tail)).compose ht).compose hs

theorem ticks_linear (q : ℚ) : ticks q ≤ 64 * (KS.W01.ratLength q + 1) := by
  have hp := KS.W01.rational_parts_size_le_length q
  have hn : (Computability.encodeNat q.num.natAbs).length ≤ KS.W01.ratLength q := by
    change KS.W01.natPayloadLength q.num.natAbs ≤ KS.W01.ratLength q
    rw [KS.W01.natPayloadLength_eq_size]
    exact hp.1
  have hd : (Computability.encodeNat q.den).length ≤ KS.W01.ratLength q := by
    change KS.W01.natPayloadLength q.den ≤ KS.W01.ratLength q
    rw [KS.W01.natPayloadLength_eq_size]
    exact hp.2
  unfold ticks
  omega

theorem linear_spec (q : ℚ) (eps : Bool) (tail : List Bool) :
    RunSpec program (inputState (KS.W01.encodeRat q) (eps :: tail))
      (outputState (KS.W01.encodeRat (signedRational eps q)) (eps :: tail))
      (64 * (KS.W01.ratLength q + 1)) :=
  (full_spec q eps tail).mono (ticks_linear q)

theorem negation_spec (q : ℚ) (tail : List Bool) :
    RunSpec program (inputState (KS.W01.encodeRat q) (false :: tail))
      (outputState (KS.W01.encodeRat (-q)) (false :: tail))
      (64 * (KS.W01.ratLength q + 1)) := linear_spec q false tail

end KS.W16.RationalSignAction

end OAI
