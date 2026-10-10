import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SourcePrograms

namespace OAI

/-! Literal serialization of rational lattice graphs into the published source
format. The constant matrix offset is subtracted from both thresholds. -/

noncomputable section
namespace ContinuumCoulomb.QuantumLatticeSerialization
open ExactQuantumFactoring.BitStackProgram
open MediatorListProgram

abbrev Coordinate := ℤ × ℤ
abbrev Input := List Coordinate × (List Bond × (ℚ × (ℚ × ℚ)))
def coordinateCode : Coordinate → List Bool := prodCode intCode intCode
def thresholdCode : (ℚ × (ℚ × ℚ)) → List Bool := prodCode ratCode (prodCode ratCode ratCode)
def inputCode : Input → List Bool :=
  prodCode (listCode coordinateCode) (prodCode (listCode bondCode) thresholdCode)

def edge (b : Bond) : BinaryHeisenbergEdge := ⟨b.1,b.2.1,BinaryRational.ofRat b.2.2⟩
def value (x : Input) : BinaryHeisenberg where
  coordinate := x.1
  edges := x.2.1.map edge
  lower := BinaryRational.ofRat (x.2.2.1-x.2.2.2.2)
  upper := BinaryRational.ofRat (x.2.2.2.1-x.2.2.2.2)

noncomputable def rationalProgram : Procedure ratCode binaryRationalCodec.encode BinaryRational.ofRat :=
  ((EncodingPrograms.appendPair BinaryEncoding.integer BinaryEncoding.natural).comp
    ((EncodingPrograms.integerOutput.comp Procedure.ratNum).pair
      (EncodingPrograms.naturalOutput.comp Procedure.ratDen))).result (by intro q; rfl)

noncomputable def coordinateProgram : Procedure coordinateCode SourcePrograms.coordinateCodec.encode id :=
  ((EncodingPrograms.appendPair BinaryEncoding.integer BinaryEncoding.integer).comp
    ((EncodingPrograms.integerOutput.comp (Procedure.first _ _)).pair
      (EncodingPrograms.integerOutput.comp (Procedure.second _ _)))).congrFun (by rintro ⟨x,y⟩; rfl)

noncomputable def edgeProgram : Procedure bondCode binaryHeisenbergEdgeCodec.encode edge := by
  let tail := Procedure.second Nat.bits (prodCode Nat.bits ratCode)
  let right := EncodingPrograms.naturalOutput.comp ((Procedure.first _ _).comp tail)
  let weight := rationalProgram.comp ((Procedure.second _ _).comp tail)
  let rest := (EncodingPrograms.appendPair BinaryEncoding.natural binaryRationalCodec).comp (right.pair weight)
  exact ((EncodingPrograms.appendPair BinaryEncoding.natural
    (BinaryEncoding.pair BinaryEncoding.natural binaryRationalCodec)).comp
      ((EncodingPrograms.naturalOutput.comp (Procedure.first _ _)).pair rest)).result (by intro b; rfl)

noncomputable def coordinatesProgram : Procedure inputCode SourcePrograms.coordinateListCodec.encode Prod.fst :=
  ((PrefixListPrograms.listOutput SourcePrograms.coordinateCodec (0,0)).comp
    ((Procedure.listMap (0,0) (0,0) coordinateProgram).comp
      (Procedure.first _ _))).congrFun (by intro x; simp)

noncomputable def bondsProgram : Procedure inputCode SourcePrograms.edgeListCodec.encode
    (fun x => x.2.1.map edge) :=
  (PrefixListPrograms.listOutput binaryHeisenbergEdgeCodec ⟨0,0,⟨0,1⟩⟩).comp
    ((Procedure.listMap (0,0,0) ⟨0,0,⟨0,1⟩⟩ edgeProgram).comp
      ((Procedure.first _ _).comp (Procedure.second _ _)))

noncomputable def thresholdsProgram : Procedure inputCode SourcePrograms.thresholdCodec.encode
    (fun x => ((value x).lower,(value x).upper)) := by
  let t : Procedure inputCode thresholdCode (fun x => x.2.2) :=
    (Procedure.second _ _).comp (Procedure.second _ _)
  let a := (Procedure.first _ _).comp t
  let b := (Procedure.first _ _).comp ((Procedure.second _ _).comp t)
  let c := (Procedure.second _ _).comp ((Procedure.second _ _).comp t)
  let lower := rationalProgram.comp (Procedure.ratSub.comp (a.pair c))
  let upper := rationalProgram.comp (Procedure.ratSub.comp (b.pair c))
  exact (EncodingPrograms.appendPair binaryRationalCodec binaryRationalCodec).comp (lower.pair upper)

noncomputable def program : Procedure inputCode binaryHeisenbergCodec.encode value := by
  let tail := (EncodingPrograms.appendPair SourcePrograms.edgeListCodec SourcePrograms.thresholdCodec).comp
    (bondsProgram.pair thresholdsProgram)
  exact ((EncodingPrograms.appendPair SourcePrograms.coordinateListCodec SourcePrograms.sourceTailCodec).comp
    (coordinatesProgram.pair tail)).result (by intro x; rfl)

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode binaryHeisenbergCodec.encode value :=
  program.toTM2

@[simp] theorem lower_value (x : Input) : (value x).lower.value = x.2.2.1-x.2.2.2.2 :=
  BinaryRational.value_ofRat _
@[simp] theorem upper_value (x : Input) : (value x).upper.value = x.2.2.2.1-x.2.2.2.2 :=
  BinaryRational.value_ofRat _
@[simp] theorem edges_length (x : Input) : (value x).edges.length = x.2.1.length := by simp [value]

end ContinuumCoulomb.QuantumLatticeSerialization

end

end OAI
