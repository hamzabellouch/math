import OAI.Combinatorics.ContingencyTables.Counting.CompanionStateMultiplierProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedLabelWeightProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleAcceptance

namespace OAI

/-! # The executed multiplier times labelled weight

Both factors are computed from the supplied current state. The matrix
lookup and the oracle consume no hidden finite-state enumeration.
-/

namespace ContingencyTables.CompanionEvaluatedWeightProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CompanionMultiplierMatrixProgram

abbrev Frame := RootedLabelWeightProgram.Config × FractionMatrix
abbrev Input := (Frame × List ℕ) × List Bool

def multiplierInput (z : Input) : CompanionStateMultiplierProgram.Input :=
  (z.1.1.2,(PairedCatalogProgram.catalog z.1.2,z.1.2))
def multiplierInputRealizer : Realizer multiplierInput :=
  pair (composition (composition first first) second)
    (pair (composition (f := fun z : Input => z.1.2) (g := PairedCatalogProgram.catalog)
      (composition first second) PairedCatalogProgram.catalogRealizer) (composition first second))
lemma polynomial_multiplierInput : PolynomialTime multiplierInputRealizer :=
  polynomial_pair (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_pair (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      PairedCatalogProgram.polynomial_catalog) (polynomial_composition polynomial_first polynomial_second))

def multiplier (z : Input) : TreeFraction.Fraction :=
  CompanionStateMultiplierProgram.output (multiplierInput z)
def multiplierRealizer : Realizer multiplier :=
  composition (f := multiplierInput) (g := CompanionStateMultiplierProgram.output)
    multiplierInputRealizer CompanionStateMultiplierProgram.outputRealizer
lemma polynomial_multiplier : PolynomialTime multiplierRealizer :=
  polynomial_composition polynomial_multiplierInput CompanionStateMultiplierProgram.polynomial_output

def weightInput (z : Input) : RootedLabelWeightProgram.Input := (z.1.1.1,(z.1.2,z.2))
def weightInputRealizer : Realizer weightInput :=
  pair (composition (composition first first) first) (pair (composition first second) second)
lemma polynomial_weightInput : PolynomialTime weightInputRealizer :=
  polynomial_pair (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second)

attribute [local irreducible] weightInput RootedLabelWeightProgram.output

def weight (z : Input) : TreeFraction.Fraction := RootedLabelWeightProgram.output (weightInput z)
def weightRealizer : Realizer weight :=
  composition (f := weightInput) (g := RootedLabelWeightProgram.output)
    weightInputRealizer RootedLabelWeightProgram.outputRealizer
lemma polynomial_weight : PolynomialTime weightRealizer :=
  polynomial_composition polynomial_weightInput RootedLabelWeightProgram.polynomial_output

attribute [local irreducible] multiplier weight

def output (z : Input) : TreeFraction.Fraction := TreeFraction.mul (multiplier z,weight z)
def outputRealizer : Realizer output :=
  composition (f := fun z : Input => (multiplier z,weight z)) (g := TreeFraction.mul)
    (pair multiplierRealizer weightRealizer) TreeFraction.mulRealizer
lemma polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair polynomial_multiplier polynomial_weight) TreeFraction.polynomial_mul

attribute [local irreducible] output

noncomputable section
open CompanionRationalUpdates
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal GridBoundary CompanionOracleDensity CommonBasesFPRAS TwoLiftStates
open FiniteObservableTransport
open scoped Classical
variable {m n : ℕ}

abbrev LabelIndex (A : Instance (Fin m) (Fin n)) :=
  Fin (CanonicalInitialEncoding.copyOrder (capacities A)).length

def sourceWeights (A : Instance (Fin m) (Fin n))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (a b : Pair A) : ℚ :=
  TreeFraction.val (w ((pairLabels A).symm a.1.1) ((pairLabels A).symm b.1.1))

lemma multiplier_code (A : Instance (Fin m) (Fin n))
    (cfg : RootedLabelWeightProgram.Config) (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : Set (Labels A × Bool)) (bits : List Bool) :
    TreeFraction.val (multiplier (((cfg,matrixCode w),encodeSet (coordinateOrder A) S),bits))=
      CommonBasesFPRAS.rationalMultiplier pairs (sourceWeights A w) S := by
  unfold multiplier multiplierInput
  rw [CompanionComputedProposal.generated_catalog]
  exact CompanionStateMultiplierProgram.output_code A (pairLabels A) (coordinateOrder A) S w

/-- Arbitrary observables of the executed weighted query agree with the
proved mathematical oracle, including outcomes on its failure event. -/
theorem sameLaw_evaluated (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A × Bool)) :
    SameLaw (fun bits : Fin (repetitionCount xi*RootedEstimatorLayoutProgram.wordWidth
      (RootedEstimatorMedianProgram.context A C K j xi (CompanionWeightOracle.profile A S) v)) → Bool =>
      TreeFraction.val (output (((RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w),
        encodeSet (coordinateOrder A) S),List.ofFn bits)))
      (RootedOracleAcceptance.evaluatedWeight A (RootedCompletion.rowColumn A.T) C K j hK hW xi
        (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S) := by
  have hw := RootedLabelWeightProgram.sameLaw_weight A C K j hC hj hK hW hB xi hxi z v
    degree depth hdegree hdepth S
  intro phi
  have he (bits : Fin (repetitionCount xi*RootedEstimatorLayoutProgram.wordWidth
      (RootedEstimatorMedianProgram.context A C K j xi (CompanionWeightOracle.profile A S) v)) → Bool) :
      TreeFraction.val (output (((RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w),
        encodeSet (coordinateOrder A) S),List.ofFn bits))=
      CommonBasesFPRAS.rationalMultiplier pairs (sourceWeights A w) S *
        TreeFraction.val (RootedLabelWeightProgram.output
          (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,
            (encodeSet (coordinateOrder A) S,List.ofFn bits))) := by
    rw [output,TreeFraction.mul_val,multiplier_code]
    unfold weight weightInput
    rfl
  simp_rw [he]
  exact hw (fun q => phi (CommonBasesFPRAS.rationalMultiplier pairs (sourceWeights A w) S*q))

end
end ContingencyTables.CompanionEvaluatedWeightProgram

end OAI
