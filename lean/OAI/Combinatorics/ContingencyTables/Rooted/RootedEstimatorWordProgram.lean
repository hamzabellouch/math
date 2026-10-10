import OAI.Combinatorics.ContingencyTables.Rooted.RootedEstimatorLayoutProgram

namespace OAI

/-! # One flat word executes the complete weight estimator

The number of generated rows is bounded by the supplied word length.
The binary schedule therefore remains safe even on malformed inputs.
-/

namespace ContingencyTables.RootedEstimatorWordProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open RootedEstimatorLayoutProgram

abbrev Input := Context×((List Bool×List Bool)×List Bool)

def phase (z : State×ℕ) : State :=
  ((z.1.1.1,((z.1.1.2.1.1,(z.1.1.2.1.2.1,z.2)),z.1.1.2.2)),z.1.2)
def phaseRealizer : Realizer phase := by
  let k : Realizer (fun z : State×ℕ => z.1.1.1) := composition (composition first first) first
  let dw : Realizer (fun z : State×ℕ => z.1.1.2.1.1) :=
    composition (composition (composition (composition first first) second) first) first
  let c : Realizer (fun z : State×ℕ => z.1.1.2.1.2.1) :=
    composition (composition (composition (composition (composition first first) second) first) second) first
  let demand : Realizer (fun z : State×ℕ => z.1.1.2.2) :=
    composition (composition (composition first first) second) second
  exact pair (pair k (pair (pair dw (pair c second)) demand)) (composition first second)
lemma polynomial_phase : PolynomialTime phaseRealizer := by
  unfold phaseRealizer
  exact polynomial_pair
    (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      (polynomial_pair
        (polynomial_pair
          (polynomial_composition (polynomial_composition (polynomial_composition
            (polynomial_composition polynomial_first polynomial_first) polynomial_second)
              polynomial_first) polynomial_first)
          (polynomial_pair
            (polynomial_composition (polynomial_composition (polynomial_composition
              (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
                polynomial_second) polynomial_first) polynomial_second) polynomial_first)
            polynomial_second))
        (polynomial_composition (polynomial_composition
          (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second)))
    (polynomial_composition polynomial_first polynomial_second)

def ratioPrefix (z : Input) : List Bool := z.2.2.take (ratioBankWidth z.1)
def ratioPrefixRealizer : Realizer ratioPrefix :=
  composition (f := fun z : Input => (z.2.2,ratioBankWidth z.1))
    (g := fun p : List Bool×ℕ => p.1.take p.2)
    (pair (composition second second)
      (composition (f := fun z : Input => z.1) (g := ratioBankWidth) first ratioBankWidthRealizer)) takeFast
lemma polynomial_ratioPrefix : PolynomialTime ratioPrefixRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
    (polynomial_composition polynomial_first polynomial_ratioBankWidth)) polynomial_takeFast

def ratioRows (z : Input) : List ℕ := completeWordRows (ratioBlockWidth z.1,ratioPrefix z)
def ratioRowsRealizer : Realizer ratioRows :=
  composition (f := fun z : Input => (ratioBlockWidth z.1,ratioPrefix z)) (g := completeWordRows)
    (pair (composition (f := fun z : Input => z.1) (g := ratioBlockWidth)
      first ratioBlockWidthRealizer) ratioPrefixRealizer) completeWordRowsRealizer
lemma polynomial_ratioRows : PolynomialTime ratioRowsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_ratioBlockWidth) polynomial_ratioPrefix)
    polynomial_completeWordRows

def ratioChunk (z : Input×ℕ) : List Bool :=
  wordChunk ((ratioBlockWidth z.1.1,ratioPrefix z.1),z.2)
def ratioChunkRealizer : Realizer ratioChunk :=
  composition (f := fun z : Input×ℕ => ((ratioBlockWidth z.1.1,ratioPrefix z.1),z.2))
    (g := wordChunk)
    (pair (pair
      (composition (f := fun z : Input×ℕ => z.1.1) (g := ratioBlockWidth)
        (composition first first) ratioBlockWidthRealizer)
      (composition (f := fun z : Input×ℕ => z.1) (g := ratioPrefix) first ratioPrefixRealizer))
      second) wordChunkRealizer
lemma polynomial_ratioChunk : PolynomialTime ratioChunkRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_ratioBlockWidth)
    (polynomial_composition polynomial_first polynomial_ratioPrefix)) polynomial_second)
    polynomial_wordChunk

def ratioState (z : Input×ℕ) : State := phase (z.1.1.1,z.2)
def ratioStateRealizer : Realizer ratioState :=
  composition (f := fun z : Input×ℕ => (z.1.1.1,z.2)) (g := phase)
    (pair (composition (composition first first) first) second) phaseRealizer
lemma polynomial_ratioState : PolynomialTime ratioStateRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_second) polynomial_phase

def ratioWords (z : Input×ℕ) : List (List Bool) := wordChunks (ratioWidth z.1.1,ratioChunk z)
def ratioWordsRealizer : Realizer ratioWords :=
  composition (f := fun z : Input×ℕ => (ratioWidth z.1.1,ratioChunk z)) (g := wordChunks)
    (pair (composition (f := fun z : Input×ℕ => z.1.1) (g := ratioWidth)
      (composition first first) ratioWidthRealizer) ratioChunkRealizer) wordChunksRealizer
lemma polynomial_ratioWords : PolynomialTime ratioWordsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_ratioWidth)
    polynomial_ratioChunk) polynomial_wordChunks

def ratioBlock (z : Input×ℕ) : RootedEstimatorBlockProgram.RatioBlock :=
  (ratioWords z).map (fun bits => (ratioState z,bits))
def ratioBlockRealizer : Realizer ratioBlock :=
  composition (f := fun z : Input×ℕ => (ratioState z,ratioWords z))
    (g := fun z : State×List (List Bool) => z.2.map (fun bits => (z.1,bits)))
    (pair ratioStateRealizer ratioWordsRealizer) (mapWith identity)
lemma polynomial_ratioBlock : PolynomialTime ratioBlockRealizer :=
  polynomial_composition (polynomial_pair polynomial_ratioState polynomial_ratioWords)
    (polynomial_mapWith polynomial_identity)

def ratioBlocks (z : Input) : List RootedEstimatorBlockProgram.RatioBlock :=
  (ratioRows z).map (fun i => ratioBlock (z,i))
def ratioBlocksRealizer : Realizer ratioBlocks :=
  composition (pair identity ratioRowsRealizer) (mapWith ratioBlockRealizer)
lemma polynomial_ratioBlocks : PolynomialTime ratioBlocksRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_ratioRows)
    (polynomial_mapWith polynomial_ratioBlock)

def correctionTail (z : Input) : List Bool := z.2.2.drop (ratioBankWidth z.1)
def correctionTailRealizer : Realizer correctionTail :=
  composition (f := fun z : Input => (z.2.2,ratioBankWidth z.1))
    (g := fun p : List Bool×ℕ => p.1.drop p.2)
    (pair (composition second second)
      (composition (f := fun z : Input => z.1) (g := ratioBankWidth) first ratioBankWidthRealizer)) dropFast
lemma polynomial_correctionTail : PolynomialTime correctionTailRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
    (polynomial_composition polynomial_first polynomial_ratioBankWidth)) polynomial_dropFast

def correctionWords (z : Input) : List (List Bool) :=
  (wordChunks (correctionWidth z.1,correctionTail z)).take z.1.2.1.2
def correctionWordsRealizer : Realizer correctionWords := by
  let chunks : Realizer (fun z : Input => wordChunks (correctionWidth z.1,correctionTail z)) :=
    composition (f := fun z : Input => (correctionWidth z.1,correctionTail z)) (g := wordChunks)
      (pair (composition (f := fun z : Input => z.1) (g := correctionWidth)
        first correctionWidthRealizer) correctionTailRealizer) wordChunksRealizer
  exact composition (f := fun z : Input =>
    (wordChunks (correctionWidth z.1,correctionTail z),z.1.2.1.2))
    (g := fun p : List (List Bool)×ℕ => p.1.take p.2)
    (pair chunks (composition (composition (composition first second) first) second)) takeFast
lemma polynomial_correctionWords : PolynomialTime correctionWordsRealizer := by
  unfold correctionWordsRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_correctionWidth) polynomial_correctionTail)
      polynomial_wordChunks)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_second) polynomial_first) polynomial_second))
    polynomial_takeFast

def terminalState (z : Input) : State := phase (z.1.1,z.1.2.1.1)
def terminalStateRealizer : Realizer terminalState :=
  composition (f := fun z : Input => (z.1.1,z.1.2.1.1)) (g := phase)
    (pair (composition first first)
      (composition (composition (composition first second) first) first)) phaseRealizer
lemma polynomial_terminalState : PolynomialTime terminalStateRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_second) polynomial_first) polynomial_first))
    polynomial_phase

def correctionSample (z : Input×List Bool) : RootedCorrectionSampleProgram.Input :=
  ((terminalState z.1,z.1.1.2.2.2),
    (z.1.2.1,(z.2.take (correctionWalkWidth z.1.1),z.2.drop (correctionWalkWidth z.1.1))))
def correctionSampleRealizer : Realizer correctionSample := by
  let tw : Realizer (fun z : Input×List Bool => correctionWalkWidth z.1.1) :=
    composition (f := fun z : Input×List Bool => z.1.1) (g := correctionWalkWidth)
      (composition first first) correctionWalkWidthRealizer
  let args : Realizer (fun z : Input×List Bool => (z.2,correctionWalkWidth z.1.1)) := pair second tw
  let terminal : Realizer (fun z : Input×List Bool => terminalState z.1) :=
    composition (f := fun z : Input×List Bool => z.1) (g := terminalState) first terminalStateRealizer
  exact pair
    (pair terminal (composition (composition (composition (composition first first) second) second) second))
    (pair (composition (composition first second) first)
      (pair (composition args takeFast) (composition args dropFast)))
lemma polynomial_correctionSample : PolynomialTime correctionSampleRealizer := by
  unfold correctionSampleRealizer
  exact polynomial_pair
    (polynomial_pair (polynomial_composition polynomial_first polynomial_terminalState)
      (polynomial_composition (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_second)
          polynomial_second) polynomial_second))
    (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
      (polynomial_pair
        (polynomial_composition (polynomial_pair polynomial_second
          (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
            polynomial_correctionWalkWidth)) polynomial_takeFast)
        (polynomial_composition (polynomial_pair polynomial_second
          (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
            polynomial_correctionWalkWidth)) polynomial_dropFast)))

def correctionBlock (z : Input) : RootedEstimatorBlockProgram.CorrectionBlock :=
  (correctionWords z).map (fun bits => correctionSample (z,bits))
def correctionBlockRealizer : Realizer correctionBlock :=
  composition (pair identity correctionWordsRealizer) (mapWith correctionSampleRealizer)
lemma polynomial_correctionBlock : PolynomialTime correctionBlockRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_correctionWords)
    (polynomial_mapWith polynomial_correctionSample)

def prepare (z : Input) : RootedEstimatorBlockProgram.Input :=
  ((assignmentCount z.1,ratioBlocks z),correctionBlock z)
def prepareRealizer : Realizer prepare :=
  pair (pair (composition (f := fun z : Input => z.1) (g := assignmentCount)
    first assignmentCountRealizer) ratioBlocksRealizer) correctionBlockRealizer
lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_assignmentCount) polynomial_ratioBlocks)
    polynomial_correctionBlock

attribute [local irreducible] prepare

def output (z : Input) : TreeFraction.Fraction := RootedEstimatorBlockProgram.output (prepare z)
def outputRealizer : Realizer output :=
  composition (f := prepare) (g := RootedEstimatorBlockProgram.output)
    prepareRealizer RootedEstimatorBlockProgram.outputRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_prepare RootedEstimatorBlockProgram.polynomial_output

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma phase_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    phase (RootedOracleWalkProgram.data A C 0 K z v,a)=RootedOracleWalkProgram.data A C a K z v := rfl

end
end ContingencyTables.RootedEstimatorWordProgram

end OAI
