import OAI.Computability.LoopMatching.LoopParser
import OAI.Computability.LoopMatching.RawAccumulator
import OAI.Computability.LoopMatching.BitNormalize
import OAI.Computability.LoopMatching.Approximation

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.MachineMain
open BinaryMatching.StackCode

def packBits (l : List Bool) : List Bool :=
  let b := BitNormalize.normalize l
  List.replicate b.length false ++ true :: b

@[fun_prop] theorem packBits_poly : Poly packBits := by
  unfold packBits
  fun_prop

lemma packBits_value (l : List Bool) :
    packBits l = BinaryMatching.encodeNat (BitAdd.value l) := by
  simp only [packBits,BitNormalize.normalize_eq_bits,BinaryMatching.encodeNat]

lemma packBits_length (l : List Bool) :
    (packBits l).length = 2*(BitNormalize.normalize l).length+1 := by
  simp only [packBits,List.length_append,List.length_replicate,List.length_cons]
  omega

def serialize (p : List Bool × List Bool) : List Bool := packBits p.1 ++ packBits p.2

@[fun_prop] theorem serialize_poly : Poly serialize := by
  unfold serialize
  fun_prop

lemma serialize_values (p : List Bool × List Bool) :
    serialize p = encodeOutput (BitAdd.value p.1,BitAdd.value p.2) := by
  simp only [serialize,packBits_value,encodeOutput]

lemma serialize_rawAccumulator (G : Input) :
    serialize (RawAccumulator.rawAccumulator (InputMachine.repr G)) =
      encodeOutput (Approximation.output G) := by
  obtain ⟨hq,hd⟩ := RawAccumulator.rawAccumulator_repr G
  rw [serialize_values,hq,hd]
  rfl

def rawPair (l : List Bool) : List Bool × List Bool :=
  (InputMachine.prepare l).elim ([],[true]) RawAccumulator.rawAccumulator

@[fun_prop] theorem rawPair_poly : Poly rawPair := by
  exact Poly.comp _ InputMachine.prepare
    (Poly.optionElim ([],[true]) RawAccumulator.rawAccumulator
      RawAccumulator.rawAccumulator_poly) InputMachine.prepare_poly

def runInput (l : List Bool) : List Bool := serialize (rawPair l)

@[fun_prop] theorem runInput_poly : Poly runInput := by
  unfold runInput
  fun_prop

def A (G : Input) : ℕ × ℕ :=
  if 2*G.ordinary.records.length+G.loops.length<G.n then (0,1)
  else Approximation.output G

lemma runInput_encoded (G : Input) : runInput (encodeInput G)=encodeOutput (A G) := by
  unfold runInput rawPair
  rw [InputMachine.prepare_encoded]
  unfold A
  by_cases h : 2*G.ordinary.records.length+G.loops.length<G.n
  · simp only [ite_eq_left h]
    change serialize ([],[true]) = encodeOutput (0,1)
    rw [serialize_values]
    rfl
  · simp only [ite_eq_right h]
    exact serialize_rawAccumulator G

def bitAlgorithm (b : Bits) : Bits := ⟨runInput b.data⟩

theorem bitAlgorithm_poly : Poly bitAlgorithm := by
  change Poly (fun b : Bits => Bits.mk (runInput b.data))
  exact Poly.comp Bits.mk (fun b : Bits => runInput b.data) Poly.bitsEncode
    (Poly.comp runInput Bits.data runInput_poly Poly.bitsDecode)

noncomputable def binaryRoutine : Routine Bits.data Bits.data bitAlgorithm :=
  bitAlgorithm_poly.routine

lemma bitAlgorithm_encoded (G : Input) :
    (bitAlgorithm ⟨encodeInput G⟩).data=encodeOutput (A G) :=
  runInput_encoded G

noncomputable def countingRoutine : Routine encodeInput encodeOutput A :=
  binaryRoutine.reindex encodeInput encodeOutput A (fun G => Bits.mk (encodeInput G))
    (fun _ => rfl) bitAlgorithm_encoded

theorem computational_endpoint :
    ∃ machine : Turing.TM2ComputableInPolyTime encodeInput encodeOutput A,
      (∀ k, Finite (machine.tm.Γ k)) ∧
      (∃ P : Polynomial ℕ, ∀ G,
        (encodeOutput (A G)).length ≤ P.eval (encodeInput G).length) := by
  refine ⟨countingRoutine.machine,countingRoutine.machine_alphabets_finite,?_⟩
  refine ⟨Polynomial.X+countingRoutine.time,?_⟩
  intro G
  simpa only [Polynomial.eval_add,Polynomial.eval_X] using countingRoutine.length_bound G

end LoopMatching.MachineMain

end OAI
