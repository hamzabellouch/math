import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.SourceNormalizationProgram

namespace OAI

/-! The actual source parser computes unary polynomial bounds from the raw
encoding length. No polynomial bound is supplied as an unverified oracle. -/

namespace ContinuumCoulomb.SourceMetadataProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

def size (d : BinaryHeisenberg) : ℕ := (binaryHeisenbergCodec.encode d).length + 1

noncomputable opaque sizeProgram : Procedure binaryHeisenbergCodec.encode unaryCode size :=
  Procedure.unarySuccessor.comp (Procedure.length.precompose binaryHeisenbergCodec.encode)

noncomputable def boundProgram : (k : ℕ) → Procedure binaryHeisenbergCodec.encode unaryCode
    (fun d => size d ^ k)
  | 0 => Procedure.constant _ unaryCode 1
  | k + 1 => (SourceNormalizationProgram.mul.comp ((boundProgram k).pair sizeProgram)).congrFun
      (by intro d; exact (pow_succ (size d) k).symm)

noncomputable opaque vertexCount : Procedure binaryHeisenbergCodec.encode unaryCode
    (fun d => d.coordinate.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength
    SourcePrograms.coordinateCodec.encode (0, 0)).comp SourcePrograms.coordinates
noncomputable opaque edgeCount : Procedure binaryHeisenbergCodec.encode unaryCode
    (fun d => d.edges.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength
    binaryHeisenbergEdgeCodec.encode ⟨0, 0, ⟨0, 1⟩⟩).comp SourcePrograms.edges

def input (k : ℕ) (d : BinaryHeisenberg) : Input :=
  ((d.edges.length, size d ^ k, size d ^ k, d.coordinate.length),
    d.edges.map (fun e => (e.left, e.right, e.coefficient.value)))

noncomputable opaque environment (k : ℕ) : Procedure binaryHeisenbergCodec.encode envCode
    (fun d => (input k d).1) :=
  edgeCount.pair ((boundProgram k).pair ((boundProgram k).pair vertexCount))
noncomputable opaque inputProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode inputCode
    (input k) := (environment k).pair MediatorListProgram.sourceBonds

noncomputable def normalizedProgram (k : ℕ) : Procedure binaryHeisenbergCodec.encode inputCode
    (fun d => SourceNormalizationProgram.normalized (input k d)) :=
  SourceNormalizationProgram.normalizedProgram.comp (inputProgram k)
noncomputable def certificate (k : ℕ) : Turing.TM2ComputableInPolyTime
    binaryHeisenbergCodec.encode inputCode
    (fun d => SourceNormalizationProgram.normalized (input k d)) :=
  (normalizedProgram k).toTM2

end ContinuumCoulomb.SourceMetadataProgram

end OAI
