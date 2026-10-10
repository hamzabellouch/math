import OAI.Combinatorics.ContingencyTables.Counting.CountingSettingsCorrect
import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleWalkProgram

namespace OAI

/-! # Constructing the immutable rooted state from the public bounded input -/

namespace ContingencyTables.CountingPreparedState
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
abbrev Input := CountingBaseProgram.Input

def catalog (z : Input) : RootedForestCatalog.Data := CountingComputedSettings.catalog z
def catalogRealizer : Realizer catalog := CountingComputedSettings.catalogRealizer
lemma polynomial_catalog : PolynomialTime catalogRealizer := CountingComputedSettings.polynomial_catalog

def baseline (z : Input) : MatrixCode := TightenedInputProgram.baseline z.1
def baselineRealizer : Realizer baseline :=
  composition (f := fun z : Input => z.1) (g := TightenedInputProgram.baseline)
    first TightenedInputProgram.baselineRealizer
lemma polynomial_baseline : PolynomialTime baselineRealizer :=
  polynomial_composition polynomial_first TightenedInputProgram.polynomial_baseline

def capacity (z : Input) : MatrixCode := (catalog z).2
def capacityRealizer : Realizer capacity := composition catalogRealizer second
lemma polynomial_capacity : PolynomialTime capacityRealizer := polynomial_composition polynomial_catalog polynomial_second

def zeroMatrix (z : Input) : MatrixCode := (capacity z).map (fun row => row.map (fun _ => 0))
def zeroMatrixRealizer : Realizer zeroMatrix :=
  composition capacityRealizer (map (map (constant 0)))
lemma polynomial_zeroMatrix : PolynomialTime zeroMatrixRealizer :=
  polynomial_composition polynomial_capacity (polynomial_map (polynomial_map (polynomial_constant 0)))

def demand (z : Input) : RootedDemandProgram.Input :=
  (catalog z,(baseline z,(zeroMatrix z,capacity z)))
def demandRealizer : Realizer demand := pair catalogRealizer (pair baselineRealizer (pair zeroMatrixRealizer capacityRealizer))
lemma polynomial_demand : PolynomialTime demandRealizer :=
  polynomial_pair polynomial_catalog (polynomial_pair polynomial_baseline
    (polynomial_pair polynomial_zeroMatrix polynomial_capacity))

def parameters (z : Input) : RootedPenaltyEvaluateProgram.Parameters :=
  ((CountingBaseProgram.dimension z.1,CountingTerminalProgram.cutoff z),(CountingBaseProgram.coefficient z,0))
def parametersRealizer : Realizer parameters :=
  pair (pair (composition (f := fun z : Input => z.1) (g := CountingBaseProgram.dimension)
    first CountingBaseProgram.dimensionRealizer) CountingTerminalProgram.cutoffRealizer)
    (pair CountingBaseProgram.coefficientRealizer (constant 0))
lemma polynomial_parameters : PolynomialTime parametersRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first CountingBaseProgram.polynomial_dimension)
    CountingTerminalProgram.polynomial_cutoff) (polynomial_pair CountingBaseProgram.polynomial_coefficient
      (polynomial_constant 0))

def zeroGrid (z : Input) : List ℕ := (RootedForestCatalog.catalog (catalog z,false)).map (fun _ => 0)
def zeroGridRealizer : Realizer zeroGrid :=
  composition (composition (f := fun z : Input => (catalog z,false)) (g := RootedForestCatalog.catalog)
    (pair catalogRealizer (constant false)) RootedForestCatalog.catalogRealizer) (map (constant 0))
lemma polynomial_zeroGrid : PolynomialTime zeroGridRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair polynomial_catalog (polynomial_constant false))
    RootedForestCatalog.polynomial_catalog) (polynomial_map (polynomial_constant 0))

def state (z : Input) : RootedOracleWalkProgram.State :=
  ((CountingTerminalProgram.binCount z,(parameters z,demand z)),zeroGrid z)
def stateRealizer : Realizer state :=
  pair (pair CountingTerminalProgram.binCountRealizer (pair parametersRealizer demandRealizer)) zeroGridRealizer
lemma polynomial_state : PolynomialTime stateRealizer :=
  polynomial_pair (polynomial_pair CountingTerminalProgram.polynomial_binCount
    (polynomial_pair polynomial_parameters polynomial_demand)) polynomial_zeroGrid

def output (z : Input) : RootedOracleWalkProgram.State×CountingPhaseParametersProgram.Input :=
  (state z,CountingComputedSettings.parameters z)
def outputRealizer : Realizer output := pair stateRealizer CountingComputedSettings.parametersRealizer
lemma polynomial_output : PolynomialTime outputRealizer :=
  polynomial_pair polynomial_state CountingComputedSettings.polynomial_parameters

open CompanionFactorialApplication ForestAssignmentSplit
open scoped Classical
variable {m n : ℕ}

lemma demand_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    demand (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      RootedDemandProgram.data (ComputedCountingParameters.data hEK r c b hne epsilon he)
        (fun _ _ => 0) (ComputedCountingParameters.data hEK r c b hne epsilon he).b := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  have hc : catalog (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=RootedForestCatalog.data A :=
    CountingComputedSettings.catalog_data hEK r c b hne epsilon he
  have hb : baseline (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      matrixCode (fun i j => (A.X i j).toNat) := by
    exact ComputedRootedInput.baseline_instance hEK r c b hne _ (ComputedCountingParameters.cutoff_two r c b epsilon he)
  have hcap : capacity (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=matrixCode A.b := by
    rw [capacity,hc]
    rfl
  have hz : zeroMatrix (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=matrixCode (fun (_ : Fin m) (_ : Fin n) => 0) := by
    rw [zeroMatrix,hcap]
    simp only [matrixCode,List.map_ofFn,Function.comp_def]
  unfold demand RootedDemandProgram.data
  rw [hc,hb,hz,hcap]

noncomputable def start (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0 < K) :
    GridBoundary.Grid (I := Fin (RootedCatalogGrid.freeCount A)) K :=
  fun _ => ⟨0,le_rfl,by omega⟩

lemma state_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let C := ComputedCountingParameters.coefficient r c b epsilon
    let K := ComputedCountingParameters.binCount r c b epsilon
    state (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      RootedOracleWalkProgram.data A C 0 K (fun _ => 0)
        (start A K (ComputedCountingParameters.binCount_pos r c b epsilon he)) := by
  dsimp only
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  have hp : parameters (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ((A.d,A.W),(ComputedCountingParameters.coefficient r c b epsilon,0)) := by
    unfold parameters
    rw [CountingBaseProgram.dimension_data,CountingTerminalProgram.cutoff_data r c b epsilon he,
      CountingBaseProgram.coefficient_data r c b epsilon he]
    rfl
  have hz : ForestCountIdentification.smallX A.small (fun _ => 0)=(fun _ _ => 0) := by
    funext i j
    simp [ForestCountIdentification.smallX]
  have hq : (fun i j => A.b i j-ForestCountIdentification.smallY A.small (fun _ => 0) i j)=A.b := by
    funext i j
    simp [ForestCountIdentification.smallY]
  unfold state RootedOracleWalkProgram.data
  rw [CountingTerminalProgram.binCount_data r c b epsilon he,hp,hz,hq,demand_data hEK r c b hne epsilon he]
  apply congrArg (fun coords => ((ComputedCountingParameters.binCount r c b epsilon,
    (((A.d,A.W),(ComputedCountingParameters.coefficient r c b epsilon,0)),
      RootedDemandProgram.data A (fun _ _ => 0) A.b)),coords))
  unfold zeroGrid catalog
  rw [CountingComputedSettings.catalog_data hEK r c b hne epsilon he]
  simp [DensePrograms.gridNatCode,start,GridBoundary.corner,RootedCatalogGrid.freeCount]

lemma start_transport (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let K := ComputedCountingParameters.binCount r c b epsilon
    RootedCatalogGrid.gridEquiv A K
      (start A K (ComputedCountingParameters.binCount_pos r c b epsilon he))=
        ComputedCountingParameters.start hEK r c b hne epsilon he := by
  rfl

end ContingencyTables.CountingPreparedState

end OAI
