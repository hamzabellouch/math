import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.UnitBinaryInclusion
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SourcePrograms
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.HardnessComposition

namespace OAI

/-! Literal polynomial-time inclusion of unit-charge Coulomb instances
into the binary-charge promise. The machine parses the position list,
attaches charge one to each position and preserves the entire encoded
electron/threshold tail. -/

namespace ContinuumCoulomb.UnitBinaryProgram
open ExactQuantumFactoring.BitStackProgram

abbrev positionListCodec := BinaryEncoding.list binaryPositionCodec
abbrev nucleusCodec := BinaryEncoding.pair binaryPositionCodec BinaryEncoding.natural
abbrev nucleusListCodec := BinaryEncoding.list nucleusCodec
abbrev tailCodec := BinaryEncoding.pair BinaryEncoding.unary SourcePrograms.thresholdCodec

def zeroPosition : BinaryPosition := ⟨⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩⟩

noncomputable opaque positionSplitter : PrefixPrograms.Splitter binaryPositionCodec :=
  SourcePrograms.equivSplitter _ binaryPositionEquiv
    (PrefixPrograms.pair _ _ SourcePrograms.rationalSplitter
      (PrefixPrograms.pair _ _ SourcePrograms.rationalSplitter SourcePrograms.rationalSplitter))

theorem position_length_pos (p : BinaryPosition) : 0 < (binaryPositionCodec.encode p).length := by
  have hx := SourcePrograms.integer_length_pos p.x.numerator
  change 0 < ((BinaryEncoding.integer.encode p.x.numerator ++
    BinaryEncoding.natural.encode p.x.denominator) ++ _).length
  simp only [List.length_append]
  omega

noncomputable opaque positionListSplitter : PrefixPrograms.Splitter positionListCodec :=
  PrefixListPrograms.listSplitter binaryPositionCodec positionSplitter zeroPosition position_length_pos

noncomputable opaque inputTuple : Procedure unitCoulombCodec.encode
    (prodCode positionListCodec.encode tailCodec.encode) unitCoulombEquiv :=
  (SourcePrograms.pairInput positionListCodec tailCodec positionListSplitter).precompose unitCoulombEquiv

noncomputable opaque positionsRaw : Procedure unitCoulombCodec.encode positionListCodec.encode
    UnitCoulomb.nuclei := (Procedure.first _ _).comp inputTuple
noncomputable opaque tailRaw : Procedure unitCoulombCodec.encode tailCodec.encode
    (fun d => (d.electrons, d.lower, d.upper)) := (Procedure.second _ _).comp inputTuple
noncomputable opaque positions : Procedure unitCoulombCodec.encode (listCode binaryPositionCodec.encode)
    UnitCoulomb.nuclei :=
  (PrefixListPrograms.listInput binaryPositionCodec positionSplitter zeroPosition position_length_pos).comp positionsRaw

noncomputable opaque attachOne : Procedure binaryPositionCodec.encode nucleusCodec.encode
    (fun r => (r, 1)) :=
  (EncodingPrograms.appendPair binaryPositionCodec BinaryEncoding.natural).comp
    ((Procedure.identity binaryPositionCodec.encode).pair
      (Procedure.constant binaryPositionCodec.encode BinaryEncoding.natural.encode 1))

noncomputable opaque nuclei : Procedure unitCoulombCodec.encode nucleusListCodec.encode
    (fun d => d.nuclei.map (fun r => (r, 1))) :=
  (PrefixListPrograms.listOutput nucleusCodec (zeroPosition, 1)).comp
    ((Procedure.listMap zeroPosition (zeroPosition, 1) attachOne).comp positions)

noncomputable opaque program : Procedure unitCoulombCodec.encode binaryCoulombCodec.encode
    UnitCoulomb.toBinary :=
  ((EncodingPrograms.appendPair nucleusListCodec tailCodec).comp (nuclei.pair tailRaw)).result
    (by intro d; rfl)

noncomputable def certificate : Turing.TM2ComputableInPolyTime
    unitCoulombCodec.encode binaryCoulombCodec.encode UnitCoulomb.toBinary := program.toTM2

noncomputable def reduction : PolynomialManyOne
    unitCoulombCodec.encode binaryCoulombCodec.encode unitCoulombPromise binaryCoulombPromise where
  map := UnitCoulomb.toBinary
  polynomialTime := certificate
  maps_yes _ := unitBinary_yes
  maps_no _ := unitBinary_no

theorem binary_hard_of_unit (h : QMAHard unitCoulombCodec.encode unitCoulombPromise) :
    QMAHard binaryCoulombCodec.encode binaryCoulombPromise := h.of_reduction reduction

end ContinuumCoulomb.UnitBinaryProgram

end OAI
