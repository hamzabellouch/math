import OAI.Combinatorics.ContingencyTables.Counting.CompanionTransitionWidth
import OAI.Combinatorics.ContingencyTables.Counting.CompanionOrderedReturn
import OAI.Combinatorics.ContingencyTables.Counting.CompanionBoundedWalkSemantics
import OAI.Combinatorics.ContingencyTables.Machines.BooleanChunkProgram

namespace OAI

/-! # A bounded flat word for the actual capped-return program -/

namespace ContingencyTables.CompanionFlatReturnProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

abbrev Input := (CompanionBoundedWalkProgram.State × ℕ) × List Bool

def widthInput (z : Input) : CompanionMetropolisWordProgram.Input :=
  ((z.1.1.1.1,z.1.1.2),[])
def widthInputRealizer : Realizer widthInput :=
  pair (pair (composition (composition (composition first first) first) first)
    (composition (composition first first) second)) (constant [])
lemma polynomial_widthInput : PolynomialTime widthInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition
      polynomial_first polynomial_first) polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second))
    (polynomial_constant [])

def width (z : Input) : ℕ := CompanionTransitionWidth.width (widthInput z)
def widthRealizer : Realizer width :=
  composition (f := widthInput) (g := CompanionTransitionWidth.width)
    widthInputRealizer CompanionTransitionWidth.widthRealizer
lemma polynomial_width : PolynomialTime widthRealizer :=
  polynomial_composition polynomial_widthInput CompanionTransitionWidth.polynomial_width

def words (z : Input) : List (List Bool) := (wordChunks (width z,z.2)).take z.1.2
def wordsRealizer : Realizer words :=
  composition (f := fun z : Input => (wordChunks (width z,z.2),z.1.2))
    (g := fun p : List (List Bool) × ℕ => p.1.take p.2)
    (pair (composition (f := fun z : Input => (width z,z.2)) (g := wordChunks)
      (pair widthRealizer second) wordChunksRealizer) (composition first second)) takeFast
lemma polynomial_words : PolynomialTime wordsRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_pair polynomial_width polynomial_second) polynomial_wordChunks)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_takeFast

def returnInput (z : Input) : CompanionOrderedReturn.Input := (z.1.1,words z)
def returnInputRealizer : Realizer returnInput :=
  pair (composition first first) wordsRealizer
lemma polynomial_returnInput : PolynomialTime returnInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first) polynomial_words

def output (z : Input) : List ℕ := CompanionOrderedReturn.output (returnInput z)
def outputRealizer : Realizer output :=
  composition (f := returnInput) (g := CompanionOrderedReturn.output)
    returnInputRealizer CompanionOrderedReturn.outputRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_returnInput CompanionOrderedReturn.polynomial_output

noncomputable section
open CommonBasesFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram FiniteObservableTransport
open CompanionTraceWords CompanionCappedReturn TwoLiftStates GridBoundary
open scoped Classical
variable {m n : ℕ}

def stateData (A : Instance (Fin m) (Fin n)) (C K j k : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : CompanionBooleanPhase.State A) : CompanionBoundedWalkProgram.State :=
  let code := encodeSet (coordinateOrder A) S.val
  let fixed : CompanionBoundedWalkProgram.Fixed :=
    (((RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w),k),code)
  (fixed,code)

def data (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : CompanionBooleanPhase.State A) (bits : List Bool) : Input :=
  ((stateData A C K j k xi z v degree depth w S,N),bits)

lemma words_data (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : CompanionBooleanPhase.State A)
    (bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi) → Bool) :
    words (data A C K j k N xi z v degree depth w S (List.ofFn bits))=
      List.ofFn (fun i : Fin N => List.ofFn
        (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi) bits i)) := by
  unfold words width widthInput data stateData
  dsimp only
  change (wordChunks (CompanionTransitionWidth.width (CompanionMetropolisWordProgram.packed
    (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w)
      k (encodeSet (coordinateOrder A) S.val) []),List.ofFn bits)).take N=_
  rw [CompanionTransitionWidth.width_config]
  rw [wordChunks_ofFn (by unfold CompanionBooleanPhase.stepBits; omega)]
  exact List.take_of_length_le (by simp only [List.length_ofFn]; exact le_rfl)

/-- This law includes the computed return scan, missing-return fallback,
and the independent words of every step. -/
theorem output_sameLaw (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : PlainIndex (pairs : List (CompanionRationalUpdates.Pair A))) :
    SameLaw (fun bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi) → Bool =>
      output (data A C K j k N xi z v degree depth w S.val (List.ofFn bits)))
      (fun words : Fin N → (Fin (CompanionBooleanPhase.stepBits A C K j k xi) → Bool) =>
        encodeSet (coordinateOrder A)
          (returnDefault (plainPredicate pairs) S (traceStates
            (RootedBooleanPhase.step A (RootedCompletion.rowColumn A.T) C K j k hK hW xi
              (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w)) S.val (List.ofFn words))).val.val) := by
  have hh := CompanionBoundedWalkProgram.history_sameLaw A C K j k hC hj hK hW hB xi hxi z v
    degree depth hdegree hdepth w S.val N
  have hm := hh.map (fun hist => CompanionCappedReturnProgram.totalReturnCode
    ((PairedCatalogProgram.catalog (encodeSet (coordinateOrder A) S.val.val),hist),
      encodeSet (coordinateOrder A) S.val.val))
  intro phi
  let draw : (Fin N → (Fin (CompanionBooleanPhase.stepBits A C K j k xi) → Bool)) → List ℕ :=
    fun words => CompanionOrderedReturn.output
      (stateData A C K j k xi z v degree depth w S.val,List.ofFn (fun i => List.ofFn (words i)))
  have he := uniformAverage_equiv (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi))
    (fun words => phi (draw words))
  have hc : (fun bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi) → Bool =>
      phi (output (data A C K j k N xi z v degree depth w S.val (List.ofFn bits))))=
      (fun bits => phi (draw (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi) bits))) := by
    funext bits
    unfold output returnInput
    rw [words_data]
    rfl
  rw [hc]
  refine he.trans ((hm phi).trans ?_)
  apply congrArg uniformAverage
  funext words
  dsimp only
  rw [generated_catalog,CompanionOrderedReturn.totalReturnCode_ordered]

end
end ContingencyTables.CompanionFlatReturnProgram

end OAI
