import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.UnitBinaryProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.TransformedGaussList

namespace OAI

/-! Serialization of computed rational triples into the actual nuclear
position codec. The canonical numerator and positive denominator are kept
exactly; no real-coordinate oracle is used. -/

namespace ContinuumCoulomb.NuclearCoordinateOutput
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode)

def rational (q : ℚ) : BinaryRational := ⟨q.num,q.den⟩
def position (q : Triple) : BinaryPosition :=
  ⟨rational q.1,rational q.2.1,rational q.2.2⟩

theorem rational_value (q : ℚ) : (rational q).value = q := Rat.num_div_den q
theorem position_value (q : Triple) : (position q).value = ![q.1,q.2.1,q.2.2] := by
  simp only [position,BinaryPosition.value,rational_value]
theorem position_valid (q : Triple) : (position q).Valid :=
  ⟨q.1.den_pos,q.2.1.den_pos,q.2.2.den_pos⟩
theorem position_value_injective : Function.Injective (fun q => (position q).value) := by
  intro q r h
  have he := h
  change (position q).value = (position r).value at he
  rw [position_value,position_value] at he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  exact Prod.ext h0 (Prod.ext h1 h2)
theorem position_injective : Function.Injective position :=
  fun _ _ h => position_value_injective (congrArg BinaryPosition.value h)

theorem real_position (q : Triple) : realPosition (position q).value = CappedKernelProgram.position q := by
  rw [position_value]
  ext i
  fin_cases i <;> rfl

noncomputable opaque rationalProgram : Procedure ratCode binaryRationalCodec.encode rational := by
  let num := EncodingPrograms.integerOutput.comp Procedure.ratNum
  let den := EncodingPrograms.naturalOutput.comp Procedure.ratDen
  let p := (EncodingPrograms.appendPair BinaryEncoding.integer BinaryEncoding.natural).comp (num.pair den)
  exact p.result (by intro q; rfl)

noncomputable opaque positionProgram : Procedure tripleCode binaryPositionCodec.encode position := by
  let x := rationalProgram.comp EulerRegisters.tripleFirstProgram
  let y := rationalProgram.comp EulerRegisters.tripleSecondProgram
  let z := rationalProgram.comp EulerRegisters.tripleThirdProgram
  let yz := (EncodingPrograms.appendPair binaryRationalCodec binaryRationalCodec).comp (y.pair z)
  let p := (EncodingPrograms.appendPair binaryRationalCodec
    (BinaryEncoding.pair binaryRationalCodec binaryRationalCodec)).comp (x.pair yz)
  exact p.result (by intro q; rfl)

def positions (qs : List Triple) : List BinaryPosition := qs.map position

noncomputable opaque positionsProgram : Procedure (listCode tripleCode)
    (BinaryEncoding.list binaryPositionCodec).encode positions :=
  (PrefixListPrograms.listOutput binaryPositionCodec UnitBinaryProgram.zeroPosition).comp
    (Procedure.listMap (0,(0,0)) UnitBinaryProgram.zeroPosition positionProgram)

theorem positions_length (qs : List Triple) : (positions qs).length = qs.length := by
  simp only [positions,List.length_map]
theorem positions_valid (qs : List Triple) {p : BinaryPosition} (hp : p ∈ positions qs) : p.Valid := by
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hp
  exact position_valid q
theorem positions_nodup {qs : List Triple} (hqs : qs.Nodup) : (positions qs).Nodup :=
  hqs.map position_injective

noncomputable def certificate : Turing.TM2ComputableInPolyTime (listCode tripleCode)
    (BinaryEncoding.list binaryPositionCodec).encode positions := positionsProgram.toTM2

end ContinuumCoulomb.NuclearCoordinateOutput

end OAI
