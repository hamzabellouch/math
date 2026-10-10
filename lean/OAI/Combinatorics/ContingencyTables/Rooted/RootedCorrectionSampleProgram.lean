import OAI.Combinatorics.ContingencyTables.Rooted.RootedCorrectionSemantics
import OAI.Combinatorics.ContingencyTables.Rooted.RootedBinDrawLaw
import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleFlatProgram

namespace OAI

/-! # Executing one selected-root correction sample

Separate finite words drive the grid walk and the integer draw. The
computed final bin and sampled integer are then passed to the exact
population and rational-power correction program.
-/

namespace ContingencyTables.RootedCorrectionSampleProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

abbrev State := RootedOracleWalkProgram.State
abbrev Input := (State × ℕ) × ((List Bool × List Bool) × (List Bool × List Bool))

def walked (z : Input) : State :=
  RootedOracleWalkProgram.flatWalk (z.1.1,z.2.2.1)
def walkedRealizer : Realizer walked :=
  composition (f := fun z : Input => (z.1.1,z.2.2.1))
    (g := RootedOracleWalkProgram.flatWalk)
    (pair (composition first first) (composition (composition second second) first))
    RootedOracleWalkProgram.flatWalkRealizer
lemma polynomial_walked : PolynomialTime walkedRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
      polynomial_first)) RootedOracleWalkProgram.polynomial_flatWalk

attribute [local irreducible] walked

def binFrame (z : Input) : RootedBinFramesProgram.Input :=
  (((walked z).1.1,(z.1.2,(walked z).1.2.1.1.1)),
    ((walked z).1.2.2.1,(walked z).2))
def binFrameRealizer : Realizer binFrame := by
  let k : Realizer (fun z : Input => (walked z).1.1) :=
    composition (composition walkedRealizer first) first
  let d : Realizer (fun z : Input => (walked z).1.2.1.1.1) :=
    composition (composition (composition (composition (composition walkedRealizer first)
      second) first) first) first
  let catalog : Realizer (fun z : Input => (walked z).1.2.2.1) :=
    composition (composition (composition (composition walkedRealizer first) second) second) first
  exact pair (pair k (pair (composition first second) d))
    (pair catalog (composition walkedRealizer second))
lemma polynomial_binFrame : PolynomialTime binFrameRealizer := by
  unfold binFrameRealizer
  exact polynomial_pair
    (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_walked polynomial_first)
        polynomial_first)
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        (polynomial_composition (polynomial_composition (polynomial_composition
          (polynomial_composition (polynomial_composition polynomial_walked polynomial_first)
            polynomial_second) polynomial_first) polynomial_first) polynomial_first)))
    (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_walked polynomial_first) polynomial_second)
          polynomial_second) polynomial_first)
      (polynomial_composition polynomial_walked polynomial_second))

attribute [local irreducible] binFrame

def sampled (z : Input) : List ℕ := RootedBinFramesProgram.draw (binFrame z,z.2.2.2)
def sampledRealizer : Realizer sampled :=
  composition (f := fun z : Input => (binFrame z,z.2.2.2))
    (g := RootedBinFramesProgram.draw)
    (pair binFrameRealizer (composition (composition second second) second))
    RootedBinFramesProgram.drawRealizer
lemma polynomial_sampled : PolynomialTime sampledRealizer :=
  polynomial_composition (polynomial_pair polynomial_binFrame
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
      polynomial_second)) RootedBinFramesProgram.polynomial_draw

attribute [local irreducible] sampled

def prepare (z : Input) : RootedCorrectionProgram.Input :=
  ((walked z,sampled z),z.2.1)
def prepareRealizer : Realizer prepare :=
  pair (pair walkedRealizer sampledRealizer) (composition second first)
lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair polynomial_walked polynomial_sampled)
    (polynomial_composition polynomial_second polynomial_first)

attribute [local irreducible] prepare

def output (z : Input) : TreeFraction.Fraction := RootedCorrectionProgram.output (prepare z)
def outputRealizer : Realizer output :=
  composition (f := prepare) (g := RootedCorrectionProgram.output)
    prepareRealizer RootedCorrectionProgram.outputRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_prepare RootedCorrectionProgram.polynomial_output

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity FairBits
open scoped BigOperators

noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (h : ℕ)
    (degree depth walkBits binBits : List Bool) : Input :=
  ((RootedOracleWalkProgram.data A C a K z v,h),((degree,depth),(walkBits,binBits)))

lemma walked_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) (degree depth : List Bool) (N : ℕ)
    (walkBits : Fin (N*oracleStepBits A C) → Bool) (binBits : List Bool) :
    walked (data A C a K z v h degree depth (List.ofFn walkBits) binBits)=
      RootedOracleWalkProgram.data A C a K z
        (RootedOracleWalkProgram.flatGridWalk A C a z v N walkBits) := by
  unfold walked data
  exact RootedOracleWalkProgram.flatWalk_data A C a K hC z v N walkBits

lemma binFrame_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) (degree depth : List Bool) (N : ℕ)
    (walkBits : Fin (N*oracleStepBits A C) → Bool) (binBits : List Bool) :
    binFrame (data A C a K z v h degree depth (List.ofFn walkBits) binBits)=
      RootedBinFramesProgram.data A h
        (RootedOracleWalkProgram.flatGridWalk A C a z v N walkBits) := by
  unfold binFrame
  rw [walked_data A C a K hC]
  rfl

lemma sampled_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (hK : 0 < K) (hW : 100*A.d*K ≤ A.W) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) (degree depth : List Bool) (N : ℕ)
    (walkBits : Fin (N*oracleStepBits A C) → Bool)
    (binBits : Fin (RootedBinDrawLaw.wordBits A h) → Bool) :
    sampled (data A C a K z v h degree depth (List.ofFn walkBits) (List.ofFn binBits))=
      List.ofFn (fun i => (RootedBinDrawLaw.flatDraw A K hK hW
        (RootedOracleWalkProgram.flatGridWalk A C a z v N walkBits) h binBits
        (RootedForestCatalog.freeEquiv A i)).val) := by
  unfold sampled
  rw [binFrame_data A C a K hC]
  exact RootedBinDrawLaw.program_flatDraw A K hK hW _ h binBits

lemma bin_flatDraw (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) (bits : Fin (RootedBinDrawLaw.wordBits A h) → Bool) :
    integerBin A K hK (RootedBinDrawLaw.flatDraw A K hK hW v h bits)=
      RootedCatalogGrid.gridEquiv A K v := by
  have hm := binOffsetValue_mem A K hK (RootedCatalogGrid.gridEquiv A K v)
    (fun i => scaledBitInteger (binSize A K (RootedCatalogGrid.gridEquiv A K v) i)
      (offsetBitLength (binSize A K (RootedCatalogGrid.gridEquiv A K v) i) h A.d)
      (binSize_positive A K hK hW _ i)
      (FirstSuccess.prefixWord (binBits_le A K hK _ h i)
        (RootedBinDrawLaw.reindexWords A h (RootedBinDrawLaw.wordEquiv A h bits) i)))
  exact (Finset.mem_filter.mp hm).2

theorem output_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (h : ℕ) (degree depth : List Bool) (sigma : ℚ)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree sigma)
    (hdepth : depth.length=PowerOfTwoApproximation.depth sigma) (N : ℕ)
    (walkBits : Fin (N*oracleStepBits A C) → Bool)
    (binBits : Fin (RootedBinDrawLaw.wordBits A h) → Bool) :
    TreeFraction.val (output (data A C a K z v h degree depth
      (List.ofFn walkBits) (List.ofFn binBits)))=
      RootedOracleDensity.computedCorrection A (RootedCompletion.rowColumn A.T) C a z K hK sigma
        (RootedBinDrawLaw.flatDraw A K hK hW
          (RootedOracleWalkProgram.flatGridWalk A C a z v N walkBits) h binBits) := by
  unfold output prepare
  rw [walked_data A C a K hC,sampled_data A C a K hC hK hW]
  exact RootedCorrectionProgram.output_data A C a K hC haH hK hB z _ _ degree depth sigma
    hdegree hdepth (bin_flatDraw A K hK hW _ h binBits)

end
end ContingencyTables.RootedCorrectionSampleProgram

end OAI
