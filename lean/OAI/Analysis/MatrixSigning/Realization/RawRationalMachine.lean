import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalCompareProgram
import OAI.Analysis.MatrixSigning.Arithmetic.RationalMagnitudeCorrect
import OAI.Analysis.MatrixSigning.Arithmetic.SignedRationalSerializer
import OAI.Analysis.MatrixSigning.Realization.DenseInputMachine

namespace OAI

namespace CurrentKS.RawRationalMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare (negativeBit constructorBits)
open KS.W19

def state (source num den sign : List Bool) : Fin 14 → List Bool :=
  ![[],[],[],[],[],[],[],[],[],[],num,den,sign,source]

def corePorts : Fin 13 ↪ Fin 14 := ⟨Fin.castSucc, Fin.castSucc_injective 13⟩
def numPorts : Fin 3 ↪ Fin 14 := ⟨![13,10,9], by decide⟩
def denPorts : Fin 3 ↪ Fin 14 := ⟨![13,11,9], by decide⟩
def magnitudePorts : Fin 3 ↪ Fin 14 := ⟨![0,10,9], by decide⟩

def readSign : Program 14 := KS.W06.RationalCompare.signProgram 13 12
def readNumerator : Program 14 := KS.W11.FrameWireCodec.unframeProgram numPorts
def readDenominator : Program 14 := KS.W11.FrameWireCodec.unframeProgram denPorts
def parse : Program 14 := compose readSign (compose readNumerator readDenominator)
def magnitude : Program 14 := KS.W06.RationalCompare.magnitudeProgram magnitudePorts 12
def trim : Program 14 := KS.W19.FixedCanonicalize.program magnitudePorts
def normalize : Program 14 := liftPorts KS.W30.RationalMagnitudeMachine.program corePorts
def serialize : Program 14 := liftPorts KS.W01.SignedRationalSerializer.program corePorts
def program : Program 14 := compose parse (compose magnitude (compose trim (compose normalize serialize)))

lemma entry_wire (a : RationalEntry) :
    a.encode = negativeBit a.numerator :: (KS.W01.frame (constructorBits a.numerator) ++
      KS.W01.frame (Computability.encodeNat a.denominator)) := by
  rcases a with ⟨z,d,hd⟩
  cases z <;> simp [RationalEntry.encode, CurrentKS.encodeInt, CurrentKS.encodeNat,
    DenseInputMachine.frame_eq, negativeBit, constructorBits, KS.W01.intPayload]

lemma readSign_spec (s : Bool) (tail : List Bool) :
    RunSpec readSign (state (s::tail) [] [] []) (state tail [] [] [s]) 1 := by
  have h := KS.W06.RationalCompare.sign_spec (13 : Fin 14) 12 (by decide)
    (state (s::tail) [] [] []) s tail rfl
  convert h using 1 <;> (try rfl)
  funext j
  fin_cases j <;> simp [state, KS.W06.RationalCompare.signAfter]

lemma readNumerator_spec (s : Bool) (num tail : List Bool) :
    RunSpec readNumerator (state (KS.W01.frame num++tail) [] [] [s])
      (state tail num [] [s]) (3*num.length+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec numPorts (state [] [] [] [s]) num tail
  convert h using 1 <;> (try rfl) <;> funext j <;> fin_cases j <;>
    simp [state, numPorts, KS.W28.FixedPositiveSerializer.registers]

lemma readDenominator_spec (s : Bool) (num den tail : List Bool) :
    RunSpec readDenominator (state (KS.W01.frame den++tail) num [] [s])
      (state tail num den [s]) (3*den.length+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec denPorts (state [] num [] [s]) den tail
  convert h using 1 <;> (try rfl) <;> funext j <;> fin_cases j <;>
    simp [state, denPorts, KS.W28.FixedPositiveSerializer.registers]

lemma parse_spec (a : RationalEntry) (tail : List Bool) :
    RunSpec parse (state (a.encode++tail) [] [] [])
      (state tail (constructorBits a.numerator) (Computability.encodeNat a.denominator)
        [negativeBit a.numerator])
      (3*(constructorBits a.numerator).length +
        3*(Computability.encodeNat a.denominator).length + 5) := by
  have h := (readSign_spec (negativeBit a.numerator)
    (KS.W01.frame (constructorBits a.numerator)++
      (KS.W01.frame (Computability.encodeNat a.denominator)++tail))).compose
    ((readNumerator_spec (negativeBit a.numerator) (constructorBits a.numerator)
      (KS.W01.frame (Computability.encodeNat a.denominator)++tail)).compose
      (readDenominator_spec (negativeBit a.numerator) (constructorBits a.numerator)
        (Computability.encodeNat a.denominator) tail))
  have he : a.encode++tail = negativeBit a.numerator ::
      (KS.W01.frame (constructorBits a.numerator)++
        (KS.W01.frame (Computability.encodeNat a.denominator)++tail)) := by
    rw [entry_wire]
    simp only [List.cons_append, List.append_assoc]
  rw [he]
  have ht : 1+((3*(constructorBits a.numerator).length+2)+
      (3*(Computability.encodeNat a.denominator).length+2)) =
      3*(constructorBits a.numerator).length+
        3*(Computability.encodeNat a.denominator).length+5 := by omega
  rw [ht] at h
  exact h

lemma magnitude_spec (s : Bool) (num den tail : List Bool) :
    RunSpec magnitude (state tail num den [s])
      (state tail (KS.W01.MagnitudeProgram.result s num) den [s]) (2*num.length+4) := by
  have h := KS.W06.RationalCompare.magnitude_spec magnitudePorts (12 : Fin 14)
    (state tail num den [s]) s num rfl rfl rfl rfl
  convert h using 1 <;> (try rfl)
  funext j
  fin_cases j <;> simp [state, magnitudePorts, Function.update]

lemma trim_spec (s : Bool) (num den tail : List Bool) :
    RunSpec trim (state tail num den [s])
      (state tail (Computability.encodeNat (bitsValue num)) den [s]) (2*num.length+2) := by
  have h := KS.W19.FixedCanonicalize.canonicalize_spec magnitudePorts
    (state tail [] den [s]) [] num
  convert h using 1 <;> (try rfl) <;> funext j <;> fin_cases j <;>
    simp [state, magnitudePorts, KS.W19.UnsignedPairSerializer.registers]

lemma magnitude_value (z : ℤ) :
    bitsValue (KS.W01.MagnitudeProgram.result (negativeBit z) (constructorBits z)) = z.natAbs := by
  rw [KS.W01.MagnitudeProgram.result_value]
  simp only [constructorBits, bitsValue_encodeNat]
  cases z <;> simp [negativeBit, KS.W01.intPayload, digit]

def magnitudeRecord (a : RationalEntry) : KS.W30.BinaryRational.RatBits :=
  ⟨negativeBit a.numerator, Computability.encodeNat a.numerator.natAbs,
    Computability.encodeNat a.denominator⟩

lemma magnitudeRecord_value (a : RationalEntry) : (magnitudeRecord a).value = a.value := by
  rcases a with ⟨z,d,hd⟩
  cases z <;> simp [magnitudeRecord, KS.W30.BinaryRational.RatBits.value,
    KS.W30.BinaryRational.RatBits.magnitude, bitsValue_encodeNat,
    negativeBit, RationalEntry.value, Int.cast_negSucc]
  ring

lemma state_core (tail num den : List Bool) (s : Bool) (i : Fin 13) :
    state tail num den [s] (corePorts i) = KS.W30.RationalMagnitudeMachine.state num den s i := by
  fin_cases i <;> rfl

lemma state_remaining (tail num den sign num' den' sign' : List Bool)
    (j : Fin 14) (hj : ∀ i, j ≠ corePorts i) :
    state tail num' den' sign' j = state tail num den sign j := by
  revert hj
  refine Fin.lastCases ?_ (fun i hi => ?_) j
  · intro _
    simp [state, Fin.last]
  · exact (hi i rfl).elim

lemma normalize_spec (a : RationalEntry) (tail : List Bool) (L : ℕ)
    (hn : (Computability.encodeNat a.numerator.natAbs).length ≤ L)
    (hd : (Computability.encodeNat a.denominator).length ≤ L) :
    RunSpec normalize (state tail (Computability.encodeNat a.numerator.natAbs)
      (Computability.encodeNat a.denominator) [negativeBit a.numerator])
      (state tail (Computability.encodeNat a.value.num.natAbs)
        (Computability.encodeNat a.value.den) [decide (a.value.num < 0)])
      (300*(L+1)^3) := by
  have h := KS.W30.RationalMagnitudeMachine.normalizes_to_rational_encoding
    (magnitudeRecord a) L (canonicalBits_encodeNat _) (canonicalBits_encodeNat _) hn hd
  dsimp only at h
  rw [magnitudeRecord_value] at h
  exact KS.W01.FixedPortRunSpec.lift_runSpec _ corePorts _ _
    (state tail (Computability.encodeNat a.numerator.natAbs)
      (Computability.encodeNat a.denominator) [negativeBit a.numerator])
    (state tail (Computability.encodeNat a.value.num.natAbs)
      (Computability.encodeNat a.value.den) [decide (a.value.num < 0)]) _ h
    (state_core _ _ _ _) (state_core _ _ _ _) (state_remaining _ _ _ _ _ _ _)

lemma serialize_spec (q : ℚ) (tail : List Bool) :
    RunSpec serialize (state tail (Computability.encodeNat q.num.natAbs)
      (Computability.encodeNat q.den) [decide (q.num < 0)])
      (state tail (KS.W01.encodeRat q) [] [])
      (16*((Computability.encodeNat q.num.natAbs).length+
        (Computability.encodeNat q.den).length+1)) := by
  have hb : ∀ i : Fin 13,
      state tail (Computability.encodeNat q.num.natAbs)
        (Computability.encodeNat q.den) [decide (q.num < 0)] (corePorts i) =
      KS.W01.SignedRationalSerializer.inputState (Computability.encodeNat q.num.natAbs)
        (Computability.encodeNat q.den) (decide (q.num < 0)) i := by
    intro i; fin_cases i <;> rfl
  have ha : ∀ i : Fin 13, state tail (KS.W01.encodeRat q) [] [] (corePorts i) =
      KS.W01.SignedRationalSerializer.outputState (KS.W01.encodeRat q) i := by
    intro i; fin_cases i <;> rfl
  exact KS.W01.FixedPortRunSpec.lift_runSpec _ corePorts _ _
    (state tail (Computability.encodeNat q.num.natAbs)
      (Computability.encodeNat q.den) [decide (q.num < 0)])
    (state tail (KS.W01.encodeRat q) [] []) _
    (KS.W01.SignedRationalSerializer.serializes_rational q) hb ha (state_remaining _ _ _ _ _ _ _)

def ticks (a : RationalEntry) (L : ℕ) : ℕ :=
  (3*(constructorBits a.numerator).length+3*(Computability.encodeNat a.denominator).length+5)+
    ((2*(constructorBits a.numerator).length+4)+
      ((2*(KS.W01.MagnitudeProgram.result (negativeBit a.numerator)
          (constructorBits a.numerator)).length+2)+
        ((300*(L+1)^3)+(16*((Computability.encodeNat a.value.num.natAbs).length+
          (Computability.encodeNat a.value.den).length+1)))))

theorem program_spec (a : RationalEntry) (tail : List Bool) (L : ℕ)
    (hn : (Computability.encodeNat a.numerator.natAbs).length ≤ L)
    (hd : (Computability.encodeNat a.denominator).length ≤ L) :
    RunSpec program (state (a.encode++tail) [] [] [])
      (state tail (KS.W01.encodeRat a.value) [] []) (ticks a L) := by
  have ht := trim_spec (negativeBit a.numerator)
    (KS.W01.MagnitudeProgram.result (negativeBit a.numerator) (constructorBits a.numerator))
    (Computability.encodeNat a.denominator) tail
  rw [magnitude_value] at ht
  exact (parse_spec a tail).compose
    ((magnitude_spec (negativeBit a.numerator) (constructorBits a.numerator)
      (Computability.encodeNat a.denominator) tail).compose
      (ht.compose ((normalize_spec a tail L hn hd).compose (serialize_spec a.value tail))))

end CurrentKS.RawRationalMachine

end OAI
