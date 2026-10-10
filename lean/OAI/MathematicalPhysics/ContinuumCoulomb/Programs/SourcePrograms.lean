import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PrefixListPrograms
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourcePromise
import OAI.Computability.QuantumFactoring.BitStackListMapWith

namespace OAI

/-! Literal finite-stack decoding of every source field, including counted
coordinate/edge lists and noncanonical rational pairs. The resulting
registers use the existing proved machine list and rational arithmetic. -/

namespace ContinuumCoulomb.SourcePrograms
open ExactQuantumFactoring.BitStackProgram PrefixPrograms

noncomputable def equivSplitter {α β : Type} (c : BinaryEncoding.Codec α)
    (e : β ≃ α) (p : Splitter c) : Splitter (BinaryEncoding.equiv c e) :=
  (p.precompose (fun x : β × List Bool => (e x.1, x.2))).result (by intro x; rfl)

noncomputable def fieldInput {α : Type} (c : BinaryEncoding.Codec α) (p : Splitter c) :
    Procedure c.encode c.encode id :=
  ((Procedure.first c.encode id).comp (p.precompose (fun x : α => (x, [])))).congrEncoding
    (by intro x; exact List.append_nil _) (by intro x; rfl)

noncomputable def pairInput {α β : Type} (c : BinaryEncoding.Codec α)
    (d : BinaryEncoding.Codec β) (p : Splitter c) :
    Procedure (BinaryEncoding.pair c d).encode (prodCode c.encode d.encode) id :=
  (p.precompose (fun x : α × β => (x.1, d.encode x.2))).result (by intro x; rfl)

noncomputable def rationalSplitter : Splitter binaryRationalCodec :=
  equivSplitter _ binaryRationalEquiv
    (PrefixPrograms.pair BinaryEncoding.integer BinaryEncoding.natural integer natural)

noncomputable def coordinateSplitter : Splitter (BinaryEncoding.pair BinaryEncoding.integer BinaryEncoding.integer) :=
  PrefixPrograms.pair _ _ integer integer

noncomputable def edgeSplitter : Splitter binaryHeisenbergEdgeCodec :=
  equivSplitter _ binaryHeisenbergEdgeEquiv
    (PrefixPrograms.pair _ _ natural
      (PrefixPrograms.pair _ _ natural rationalSplitter))

theorem integer_length_pos (z : ℤ) : 0 < (BinaryEncoding.integer.encode z).length := by
  cases z <;> simp only [BinaryEncoding.integer, List.length_cons] <;> omega

theorem coordinate_length_pos (p : ℤ × ℤ) :
    0 < ((BinaryEncoding.pair BinaryEncoding.integer BinaryEncoding.integer).encode p).length := by
  have h := integer_length_pos p.1
  simp only [BinaryEncoding.pair_length]
  omega

theorem edge_length_pos (e : BinaryHeisenbergEdge) :
    0 < (binaryHeisenbergEdgeCodec.encode e).length := by
  have h := BinaryEncoding.natural_length e.left
  change 0 < ((BinaryEncoding.natural.encode e.left ++
    (BinaryEncoding.natural.encode e.right ++ binaryRationalCodec.encode e.coefficient))).length
  simp only [List.length_append]
  omega

abbrev Coordinate := ℤ × ℤ

def coordinateCodec := BinaryEncoding.pair BinaryEncoding.integer BinaryEncoding.integer

def coordinateListCodec := BinaryEncoding.list coordinateCodec

def edgeListCodec := BinaryEncoding.list binaryHeisenbergEdgeCodec

def thresholdCodec := BinaryEncoding.pair binaryRationalCodec binaryRationalCodec

def sourceTailCodec := BinaryEncoding.pair edgeListCodec thresholdCodec

def sourceTupleCodec := BinaryEncoding.pair coordinateListCodec sourceTailCodec

noncomputable def coordinateListSplitter : Splitter coordinateListCodec :=
  PrefixListPrograms.listSplitter coordinateCodec coordinateSplitter (0, 0) coordinate_length_pos

noncomputable def edgeListSplitter : Splitter edgeListCodec :=
  PrefixListPrograms.listSplitter binaryHeisenbergEdgeCodec edgeSplitter ⟨0, 0, ⟨0, 1⟩⟩ edge_length_pos

noncomputable def thresholdSplitter : Splitter thresholdCodec :=
  PrefixPrograms.pair _ _ rationalSplitter rationalSplitter

noncomputable def sourceTailSplitter : Splitter sourceTailCodec :=
  PrefixPrograms.pair _ _ edgeListSplitter thresholdSplitter

noncomputable def sourceSplitter : Splitter binaryHeisenbergCodec :=
  equivSplitter _ binaryHeisenbergEquiv
    (PrefixPrograms.pair _ _ coordinateListSplitter sourceTailSplitter)

/-- The rational denominator is parsed and reduced by the actual gcd-based
machine routine, so noncanonical input fractions are handled correctly. -/
noncomputable def rationalValue : Procedure binaryRationalCodec.encode ratCode BinaryRational.value := by
  let p := (pairInput BinaryEncoding.integer BinaryEncoding.natural integer).precompose
    binaryRationalEquiv
  let numerator : Procedure binaryRationalCodec.encode intCode BinaryRational.numerator :=
    EncodingPrograms.integerInput.comp ((Procedure.first _ _).comp p)
  let denominator : Procedure binaryRationalCodec.encode Nat.bits BinaryRational.denominator :=
    EncodingPrograms.naturalInput.comp ((Procedure.second _ _).comp p)
  exact (Procedure.makeRat.comp (numerator.pair denominator)).congrFun (by
    intro q
    exact Rat.mkRat_eq_div q.numerator q.denominator)

noncomputable def sourceTuple : Procedure binaryHeisenbergCodec.encode
    (prodCode coordinateListCodec.encode sourceTailCodec.encode) binaryHeisenbergEquiv :=
  (pairInput coordinateListCodec sourceTailCodec coordinateListSplitter).precompose binaryHeisenbergEquiv

noncomputable def coordinatesRaw : Procedure binaryHeisenbergCodec.encode coordinateListCodec.encode
    BinaryHeisenberg.coordinate := (Procedure.first _ _).comp sourceTuple

noncomputable def tailRaw : Procedure binaryHeisenbergCodec.encode sourceTailCodec.encode
    (fun d => (d.edges, d.lower, d.upper)) := (Procedure.second _ _).comp sourceTuple

noncomputable def tailTuple : Procedure binaryHeisenbergCodec.encode
    (prodCode edgeListCodec.encode thresholdCodec.encode) (fun d => (d.edges, d.lower, d.upper)) :=
  (pairInput edgeListCodec thresholdCodec edgeListSplitter).comp tailRaw

noncomputable def edgesRaw : Procedure binaryHeisenbergCodec.encode edgeListCodec.encode
    BinaryHeisenberg.edges := (Procedure.first _ _).comp tailTuple

noncomputable def thresholdsRaw : Procedure binaryHeisenbergCodec.encode thresholdCodec.encode
    (fun d => (d.lower, d.upper)) := (Procedure.second _ _).comp tailTuple

noncomputable def thresholdTuple : Procedure binaryHeisenbergCodec.encode
    (prodCode binaryRationalCodec.encode binaryRationalCodec.encode) (fun d => (d.lower, d.upper)) :=
  (pairInput binaryRationalCodec binaryRationalCodec rationalSplitter).comp thresholdsRaw

noncomputable def coordinates : Procedure binaryHeisenbergCodec.encode
    (listCode coordinateCodec.encode) BinaryHeisenberg.coordinate :=
  (PrefixListPrograms.listInput coordinateCodec coordinateSplitter (0, 0) coordinate_length_pos).comp coordinatesRaw

noncomputable def edges : Procedure binaryHeisenbergCodec.encode
    (listCode binaryHeisenbergEdgeCodec.encode) BinaryHeisenberg.edges :=
  (PrefixListPrograms.listInput binaryHeisenbergEdgeCodec edgeSplitter ⟨0, 0, ⟨0, 1⟩⟩ edge_length_pos).comp edgesRaw

noncomputable def lower : Procedure binaryHeisenbergCodec.encode ratCode
    (fun d => d.lower.value) := rationalValue.comp ((Procedure.first _ _).comp thresholdTuple)

noncomputable def upper : Procedure binaryHeisenbergCodec.encode ratCode
    (fun d => d.upper.value) := rationalValue.comp ((Procedure.second _ _).comp thresholdTuple)

def registerCode (d : BinaryHeisenberg) : List Bool :=
  prodCode (listCode coordinateCodec.encode)
    (prodCode (listCode binaryHeisenbergEdgeCodec.encode) (prodCode ratCode ratCode))
      (d.coordinate, d.edges, d.lower.value, d.upper.value)

/-- A concrete polynomial TM2 parser for the entire source instance. -/
noncomputable def registers : Procedure binaryHeisenbergCodec.encode registerCode id :=
  (coordinates.pair (edges.pair (lower.pair upper))).result (by intro d; rfl)

noncomputable def registers_certificate : Turing.TM2ComputableInPolyTime
    binaryHeisenbergCodec.encode registerCode id := registers.toTM2

end ContinuumCoulomb.SourcePrograms

end OAI
