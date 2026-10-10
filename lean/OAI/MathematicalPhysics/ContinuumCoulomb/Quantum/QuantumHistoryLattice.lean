import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistorySpatial
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialLattice
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFinalPrecision

namespace OAI

/-! The actual sparse verifier compiler, through the specified planar lattice.
The final precision pays for every early and routing error; the scalar offset
is removed from both thresholds exactly. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumPaddedLabelProgram QuantumForkList QuantumAlgebraicHistory
open scoped Classical

-- Keep the fixed density symbolic; expanding it as a numeral is unnecessary.
attribute [local irreducible] spatialDensity

private theorem spatialDensity_pos (A D : ℕ) (hA : 0 < A) : 0 < spatialDensity A D := by
  unfold spatialDensity
  exact Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) D) (Nat.succ_pos D)) hA

theorem finalDensity_pos : 0 < finalDensity := spatialDensity_pos rawDensity historyDegree (by decide)

theorem iterate_count_ge (N : ℚ) (s : State) (k : ℕ) : s.1 ≤ (iterate N k s).1 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    change s.1 ≤ (iterate N k s).1+2*pairCount (iterate N k s).2.2.2
    exact ih.trans (Nat.le_add_right _ _)

theorem model_vertices_ge (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    historyQubits (qmaSparseCircuit c) hT N ≤ (model c hc hT hne N).n := by
  change _ ≤ (input c hc hT hne N).state.1
  rw [input_state]
  let s := initial (historyQubits (qmaSparseCircuit c) hT N)
    (historyOutput (qmaSparseCircuit c) hT N).1 (historyOutput (qmaSparseCircuit c) hT N).2 (N:ℚ)
  exact (show historyQubits (qmaSparseCircuit c) hT N ≤ s.1 from Nat.le_add_right _ _).trans
    (iterate_count_ge (N:ℚ) s historyDegree)

theorem model_vertices_pos (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :
    0 < (model c hc hT hne N).n := by
  have hp : 0 < historyQubits (qmaSparseCircuit c) hT N := by
    rw [historyQubits_eq,QuantumOrderedSourceIndex.qubitCount_eq]
    omega
  exact hp.trans_le (model_vertices_ge c hc hT hne N)

-- The certified value is fixed, but need never be expanded into a numeral.
private opaque routeRoundValue : { k : ℕ //
    QMASpatialExchangeModel.routeLengthBound (spatialDensity rawDensity historyDegree)
      (27*spatialDensity rawDensity historyDegree) = k } :=
  ⟨QMASpatialExchangeModel.routeLengthBound (spatialDensity rawDensity historyDegree)
    (27*spatialDensity rawDensity historyDegree),rfl⟩

def routeRounds : ℕ := routeRoundValue.val
theorem routeRounds_eq : QMASpatialExchangeModel.routeLengthBound
    (spatialDensity rawDensity historyDegree) (27*spatialDensity rawDensity historyDegree) =
      routeRounds := routeRoundValue.property
def totalRounds : ℕ := historyDegree+routeRounds+83
def latticePrecision (c : QMACircuit) : ℕ := finalPrecision totalRounds (qmaSparseCircuit c)

private theorem combine_errors (D K : ℕ) (N : ℝ) :
    ((K:ℝ)+82)/N+((D:ℝ)+10)/N = (((D+K+83:ℕ):ℝ)+9)/N := by
  push_cast
  ring

def lattice (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) :=
  (model c hc hT hne N).latticeGraph finalDensity_pos (model_degree c hc hT hne N) (N:ℚ)

theorem lattice_history_error (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) (N : ℕ) (hN : 0 < N) :
    |(lattice c hc hT hne N).energy-(qmaOrderedHistoryModel (qmaSparseCircuit c) hT).energy| ≤
      ((totalRounds:ℝ)+9)/(N:ℝ) := by
  have hr := (model c hc hT hne N).lattice_energy_error_nat finalDensity_pos
    (model_degree c hc hT hne N) N hN
  rw [routeRounds_eq] at hr
  have he := model_history_error c hc hT hne N hN
  have hr' : |(lattice c hc hT hne N).energy-(model c hc hT hne N).energy| ≤
      ((routeRounds:ℝ)+82)/(N:ℝ) := hr
  calc
    _ ≤ |(lattice c hc hT hne N).energy-(model c hc hT hne N).energy|+
      |(model c hc hT hne N).energy-(qmaOrderedHistoryModel (qmaSparseCircuit c) hT).energy| :=
        abs_sub_le _ _ _
    _ ≤ ((routeRounds:ℝ)+82)/(N:ℝ)+((historyDegree:ℝ)+10)/(N:ℝ) := add_le_add hr' he
    _ = _ := combine_errors historyDegree routeRounds (N:ℝ)

def source (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) : SquareLatticeHeisenberg :=
  (model c hc hT hne (latticePrecision c)).latticeSource finalDensity_pos
    (model_degree c hc hT hne (latticePrecision c)) (latticePrecision c:ℚ)
    (model_vertices_pos c hc hT hne (latticePrecision c))
    (xzYesThreshold (qmaSparseCircuit c)) (xzNoThreshold (qmaSparseCircuit c))
    (xz_threshold_lt (qmaSparseCircuit c))

theorem source_energy (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) :
    realSourceGroundEnergy (source c hc hT hne) =
      (lattice c hc hT hne (latticePrecision c)).energy-
        ((lattice c hc hT hne (latticePrecision c)).constant:ℝ) :=
  (model c hc hT hne (latticePrecision c)).latticeSource_energy finalDensity_pos
    (model_degree c hc hT hne (latticePrecision c)) _ _ _ _ _

theorem source_accepting (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ [])
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖=1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    realSourceGroundEnergy (source c hc hT hne) ≤ ((source c hc hT hne).lower:ℝ) := by
  have herr := lattice_history_error c hc hT hne (latticePrecision c)
    (finalPrecision_pos totalRounds (qmaSparseCircuit c))
  have he := final_accepting totalRounds (qmaSparseCircuit c) hT
    (qmaSparseCircuit_wellFormed c hc) herr psi hpsi
    ((qmaSparseCircuit_acceptance c hc psi) ▸ hacc)
  rw [source_energy]
  change _ ≤ ((xzYesThreshold (qmaSparseCircuit c)-
    (lattice c hc hT hne (latticePrecision c)).constant:ℚ):ℝ)
  push_cast
  linarith

theorem source_rejecting (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ [])
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖=1 → qmaAcceptance c hc psi ≤ 1/3) :
    ((source c hc hT hne).upper:ℝ) ≤ realSourceGroundEnergy (source c hc hT hne) := by
  have herr := lattice_history_error c hc hT hne (latticePrecision c)
    (finalPrecision_pos totalRounds (qmaSparseCircuit c))
  have he := final_rejecting totalRounds (qmaSparseCircuit c) hT
    (qmaSparseCircuit_wellFormed c hc) herr
    (by intro psi hpsi; rw [qmaSparseCircuit_acceptance]; exact hsound psi hpsi)
  rw [source_energy]
  change ((xzNoThreshold (qmaSparseCircuit c)-
    (lattice c hc hT hne (latticePrecision c)).constant:ℚ):ℝ) ≤ _
  push_cast
  linarith

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
