import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.MediatorOffsetProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceNormalizationCorrectness

namespace OAI

/-! The complete literal source-to-positive-spin program. It parses the
original source, computes the fixed polynomial metadata, rounds and deletes
zero coefficients, emits all three graph stages, and shifts both thresholds. -/

namespace ContinuumCoulomb.SourcePositiveProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

structure Registers where
  coordinate : List SourcePrograms.Coordinate
  vertices : ℕ
  bound : ℕ
  gapScale : ℕ
  bonds : List Bond
  offset : ℚ
  lower : ℚ
  upper : ℚ

def registerCode (x : Registers) : List Bool :=
  prodCode (listCode SourcePrograms.coordinateCodec.encode)
    (prodCode unaryCode (prodCode unaryCode (prodCode unaryCode
      (prodCode (listCode bondCode) (prodCode ratCode (prodCode ratCode ratCode))))))
    (x.coordinate, x.vertices, x.bound, x.gapScale, x.bonds, x.offset, x.lower, x.upper)

def normalized (k : ℕ) (d : BinaryHeisenberg) : Input :=
  SourceNormalizationProgram.normalized (SourceMetadataProgram.input k d)

def offset (k : ℕ) (d : BinaryHeisenberg) : ℚ := MediatorOffsetProgram.offset (normalized k d)

def error (k : ℕ) (d : BinaryHeisenberg) : ℚ :=
  1 / (128 * ((SourceMetadataProgram.size d ^ k : ℕ) : ℚ))

def output (k : ℕ) (d : BinaryHeisenberg) : Registers where
  coordinate := d.coordinate
  vertices := (normalized k d).1.2.2.2 + 18 * (normalized k d).1.1
  bound := MediatorParameters.finalWeight (normalized k d).1.1
    (normalized k d).1.2.1 (normalized k d).1.2.2.1
  gapScale := SourceMetadataProgram.size d ^ k
  bonds := MediatorThreeStageProgram.finalBonds (normalized k d)
  offset := offset k d
  lower := d.lower.value - offset k d + error k d
  upper := d.upper.value - offset k d - error k d

noncomputable opaque normalizedProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode inputCode
    (normalized k) := SourceMetadataProgram.normalizedProgram k
noncomputable opaque verticesProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode unaryCode
    (fun d => (output k d).vertices) :=
  MediatorThreeStageProgram.verticesProgram.comp (normalizedProgram k)
noncomputable opaque boundProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode unaryCode
    (fun d => (output k d).bound) :=
  MediatorThreeStageProgram.boundProgram.comp (normalizedProgram k)
noncomputable opaque bondsProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode (listCode bondCode)
    (fun d => (output k d).bonds) :=
  MediatorThreeStageProgram.bondsProgram.comp (normalizedProgram k)
noncomputable opaque offsetProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode ratCode
    (offset k) := MediatorOffsetProgram.offsetProgram.comp (normalizedProgram k)

noncomputable opaque gRationalProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode ratCode
    (fun d => ((SourceMetadataProgram.size d ^ k : ℕ) : ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp (SourceMetadataProgram.boundProgram k))
noncomputable opaque denominatorProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode ratCode
    (fun d => 128 * ((SourceMetadataProgram.size d ^ k : ℕ) : ℚ)) :=
  Procedure.ratMul.comp ((Procedure.constant binaryHeisenbergCodec.encode ratCode 128).pair
    (gRationalProgram k))
noncomputable opaque errorProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode ratCode (error k) :=
  Procedure.ratDiv.comp ((Procedure.constant binaryHeisenbergCodec.encode ratCode 1).pair
    (denominatorProgram k))
noncomputable opaque lowerShiftProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode ratCode
    (fun d => d.lower.value - offset k d) :=
  Procedure.ratSub.comp (SourcePrograms.lower.pair (offsetProgram k))
noncomputable opaque upperShiftProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode ratCode
    (fun d => d.upper.value - offset k d) :=
  Procedure.ratSub.comp (SourcePrograms.upper.pair (offsetProgram k))
noncomputable opaque lowerProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode ratCode
    (fun d => (output k d).lower) :=
  Procedure.ratAdd.comp ((lowerShiftProgram k).pair (errorProgram k))
noncomputable opaque upperProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode ratCode
    (fun d => (output k d).upper) :=
  Procedure.ratSub.comp ((upperShiftProgram k).pair (errorProgram k))

noncomputable opaque outputProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode registerCode
    (output k) :=
  (SourcePrograms.coordinates.pair ((verticesProgram k).pair ((boundProgram k).pair
    ((SourceMetadataProgram.boundProgram k).pair ((bondsProgram k).pair ((offsetProgram k).pair
      ((lowerProgram k).pair (upperProgram k)))))))).result (by intro d; rfl)

noncomputable def certificate (k : ℕ) : Turing.TM2ComputableInPolyTime
    binaryHeisenbergCodec.encode registerCode (output k) := (outputProgram k).toTM2

end ContinuumCoulomb.SourcePositiveProgram

end OAI
