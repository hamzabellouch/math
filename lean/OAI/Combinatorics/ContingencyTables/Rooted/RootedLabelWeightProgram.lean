import OAI.Combinatorics.ContingencyTables.Machines.PairedDemandProgram
import OAI.Combinatorics.ContingencyTables.Machines.PairedFactorialProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedEstimatorMedianLaw
import OAI.Combinatorics.ContingencyTables.Rooted.RootedWeightOracle

namespace OAI

/-! # The executed weight oracle at a current paired state

The immutable schedule and graph are shared. Each call reconstructs the
two small-cell views from its actual state, runs the independent median
estimator, and multiplies by the exact factorial ratio.
-/

namespace ContingencyTables.RootedLabelWeightProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open RootedEstimatorLayoutProgram

abbrev Config := (Context × ℕ) × (List Bool × List Bool)
abbrev Input := Config × (List ℕ × List Bool)

def replaceState (z : RootedOracleWalkProgram.State × List ℕ) : RootedOracleWalkProgram.State :=
  ((z.1.1.1,(z.1.1.2.1,PairedDemandProgram.output (z.1.1.2.2,z.2))),z.1.2)
def replaceStateRealizer : Realizer replaceState := by
  let k : Realizer (fun z : RootedOracleWalkProgram.State × List ℕ => z.1.1.1) :=
    composition (composition first first) first
  let parameters : Realizer (fun z : RootedOracleWalkProgram.State × List ℕ => z.1.1.2.1) :=
    composition (composition (composition first first) second) first
  let demands : Realizer (fun z : RootedOracleWalkProgram.State × List ℕ =>
      PairedDemandProgram.output (z.1.1.2.2,z.2)) :=
    composition (f := fun z : RootedOracleWalkProgram.State × List ℕ => (z.1.1.2.2,z.2))
      (g := PairedDemandProgram.output)
      (pair (composition (composition (composition first first) second) second) second)
      PairedDemandProgram.outputRealizer
  exact pair (pair k (pair parameters demands)) (composition first second)
lemma polynomial_replaceState : PolynomialTime replaceStateRealizer := by
  unfold replaceStateRealizer
  exact polynomial_pair
    (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      (polynomial_pair
        (polynomial_composition (polynomial_composition
          (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first)
        (polynomial_composition (polynomial_pair
          (polynomial_composition (polynomial_composition
            (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second)
          polynomial_second) PairedDemandProgram.polynomial_output)))
    (polynomial_composition polynomial_first polynomial_second)

def stateInput (z : Input) : RootedOracleWalkProgram.State × List ℕ :=
  (z.1.1.1.1,z.2.1)
def stateInputRealizer : Realizer stateInput :=
  pair (composition (composition (composition first first) first) first)
    (composition second first)
lemma polynomial_stateInput : PolynomialTime stateInputRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
    (polynomial_composition polynomial_second polynomial_first)

def context (z : Input) : Context :=
  (replaceState (stateInput z),z.1.1.1.2)
def contextRealizer : Realizer context :=
  pair (composition (f := stateInput) (g := replaceState) stateInputRealizer replaceStateRealizer)
    (composition (composition (composition first first) first) second)
lemma polynomial_context : PolynomialTime contextRealizer :=
  polynomial_pair (polynomial_composition polynomial_stateInput polynomial_replaceState)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)

def medianInput (z : Input) : RootedEstimatorMedianProgram.Input :=
  ((context z,z.1.1.2),(z.1.2,z.2.2))
def medianInputRealizer : Realizer medianInput :=
  pair (pair contextRealizer (composition (composition first first) second))
    (pair (composition first second) (composition second second))
lemma polynomial_medianInput : PolynomialTime medianInputRealizer :=
  polynomial_pair (polynomial_pair polynomial_context
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second))
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition polynomial_second polynomial_second))

def demandInput (z : Input) : PairedDemandProgram.Input :=
  ((stateInput z).1.1.2.2,z.2.1)
def demandInputRealizer : Realizer demandInput :=
  pair (composition (f := stateInput)
      (g := fun s : RootedOracleWalkProgram.State × List ℕ => s.1.1.2.2)
      stateInputRealizer (composition (composition (composition first first) second) second))
    (composition second first)
lemma polynomial_demandInput : PolynomialTime demandInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_stateInput
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second))
    (polynomial_composition polynomial_second polynomial_first)

def factorialInput (z : Input) : PairedProfileProgram.Input :=
  (CompanionCellCatalog.capacities (PairedDemandProgram.cells (demandInput z)),z.2.1)
def factorialInputRealizer : Realizer factorialInput :=
  pair (composition (f := demandInput)
    (g := fun s : PairedDemandProgram.Input => CompanionCellCatalog.capacities (PairedDemandProgram.cells s))
    demandInputRealizer (composition (f := PairedDemandProgram.cells)
      (g := CompanionCellCatalog.capacities) PairedDemandProgram.cellsRealizer
        CompanionCellCatalog.capacitiesRealizer)) (composition second first)
lemma polynomial_factorialInput : PolynomialTime factorialInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_demandInput
    (polynomial_composition PairedDemandProgram.polynomial_cells CompanionCellCatalog.polynomial_capacities))
    (polynomial_composition polynomial_second polynomial_first)

attribute [local irreducible] medianInput factorialInput

def medianResult (z : Input) : TreeFraction.Fraction := RootedEstimatorMedianProgram.output (medianInput z)
def medianResultRealizer : Realizer medianResult :=
  composition (f := medianInput) (g := RootedEstimatorMedianProgram.output)
    medianInputRealizer RootedEstimatorMedianProgram.outputRealizer
lemma polynomial_medianResult : PolynomialTime medianResultRealizer :=
  polynomial_composition polynomial_medianInput RootedEstimatorMedianProgram.polynomial_output

def factorialResult (z : Input) : TreeFraction.Fraction := PairedFactorialProgram.output (factorialInput z)
def factorialResultRealizer : Realizer factorialResult :=
  composition (f := factorialInput) (g := PairedFactorialProgram.output)
    factorialInputRealizer PairedFactorialProgram.outputRealizer
lemma polynomial_factorialResult : PolynomialTime factorialResultRealizer :=
  polynomial_composition polynomial_factorialInput PairedFactorialProgram.polynomial_output

attribute [local irreducible] medianResult factorialResult

def output (z : Input) : TreeFraction.Fraction := TreeFraction.mul (medianResult z,factorialResult z)
def outputRealizer : Realizer output :=
  composition (f := fun z : Input => (medianResult z,factorialResult z)) (g := TreeFraction.mul)
    (pair medianResultRealizer factorialResultRealizer) TreeFraction.mulRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair polynomial_medianResult polynomial_factorialResult) TreeFraction.polynomial_mul

noncomputable section
open CompanionFactorialApplication CompanionArithmeticProposal GridBoundary
open CompanionOracleDensity FiniteObservableTransport CommonBasesFPRAS
open scoped Classical
variable {m n : ℕ}

def config (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (epsilon delta : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) : Config :=
  ((RootedEstimatorMedianProgram.context A C K j epsilon z v,repetitionCount delta),(degree,depth))

lemma replaceState_data (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (S : Set (Labels A × Bool)) :
    replaceState (RootedOracleWalkProgram.data A C a K z v,
      encodeSet (CompanionComputedInitial.coordinateOrder A) S)=
        RootedOracleWalkProgram.data A C a K (CompanionWeightOracle.profile A S) v := by
  unfold replaceState RootedOracleWalkProgram.data
  rw [PairedDemandProgram.output_data]

lemma context_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (epsilon delta : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth bits : List Bool) (S : Set (Labels A × Bool)) :
    context (config A C K j epsilon delta z v degree depth,
      (encodeSet (CompanionComputedInitial.coordinateOrder A) S,bits))=
        RootedEstimatorMedianProgram.context A C K j epsilon (CompanionWeightOracle.profile A S) v := by
  unfold context stateInput config RootedEstimatorMedianProgram.context
    RootedEstimatorWordProgram.scheduledContext RootedEstimatorLayoutProgram.data
  rw [replaceState_data]

lemma output_value (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (epsilon delta : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (S : Set (Labels A × Bool))
    (bits : Fin (repetitionCount delta*wordWidth
      (RootedEstimatorMedianProgram.context A C K j epsilon (CompanionWeightOracle.profile A S) v)) → Bool) :
    TreeFraction.val (output (config A C K j epsilon delta z v degree depth,
      (encodeSet (CompanionComputedInitial.coordinateOrder A) S,List.ofFn bits)))=
      RootedEstimatorMedianProgram.value A C K j epsilon delta
        (CompanionWeightOracle.profile A S) v degree depth bits * CompanionWeightOracle.factorialRatio A S := by
  rw [output,TreeFraction.mul_val]
  unfold medianResult factorialResult
  have hf : factorialInput (config A C K j epsilon delta z v degree depth,
      (encodeSet (CompanionComputedInitial.coordinateOrder A) S,List.ofFn bits))=
        (List.ofFn (CompanionComputedInitial.capacities A),
          encodeSet (CompanionComputedInitial.coordinateOrder A) S) := by
    unfold factorialInput demandInput stateInput config RootedEstimatorMedianProgram.context
      RootedEstimatorWordProgram.scheduledContext RootedEstimatorLayoutProgram.data
      RootedOracleWalkProgram.data
    rw [PairedDemandProgram.cells_data,CompanionCellCatalog.capacities_eq]
    rfl
  rw [hf,PairedFactorialProgram.output_physical]
  apply congrArg (fun q : ℚ => q*CompanionWeightOracle.factorialRatio A S)
  unfold medianInput
  rw [context_data]
  rfl

theorem sameLaw_weight (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (S : Set (Labels A × Bool)) :
    SameLaw (fun bits : Fin (repetitionCount xi*wordWidth
      (RootedEstimatorMedianProgram.context A C K j xi (CompanionWeightOracle.profile A S) v)) → Bool =>
      TreeFraction.val (output (config A C K j xi xi z v degree depth,
      (encodeSet (CompanionComputedInitial.coordinateOrder A) S,List.ofFn bits))))
      (RootedWeightOracle.evaluate A (RootedCompletion.rowColumn A.T) C K hK hW j xi
        (RootedCatalogGrid.gridEquiv A K v) S) := by
  have h := (RootedEstimatorMedianProgram.sameLaw A C K j hC hj hK hW hB xi xi hxi
    (CompanionWeightOracle.profile A S) (CompanionWeightOracle.profile_inBox A S)
    v degree depth hdegree hdepth).map (fun q => q*CompanionWeightOracle.factorialRatio A S)
  intro phi
  have hl : (fun bits : Fin (repetitionCount xi*wordWidth
      (RootedEstimatorMedianProgram.context A C K j xi (CompanionWeightOracle.profile A S) v)) → Bool =>
      phi (TreeFraction.val (output (config A C K j xi xi z v degree depth,
      (encodeSet (CompanionComputedInitial.coordinateOrder A) S,List.ofFn bits)))))=
      (fun bits => phi (RootedEstimatorMedianProgram.value A C K j xi xi
        (CompanionWeightOracle.profile A S) v degree depth bits*CompanionWeightOracle.factorialRatio A S)) := by
    funext bits
    rw [output_value]
  rw [hl]
  exact h phi

end
end ContingencyTables.RootedLabelWeightProgram

end OAI
