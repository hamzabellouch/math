import OAI.Combinatorics.EditApproximation.Refinement.PhysicalProgramRefreshWiring
import OAI.Combinatorics.EditApproximation.Geometry.UnskippedRegretBudget

namespace OAI

/-! Actual local and global expected regret of the complete finite selection program. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

noncomputable def physicalProgramNodeCoefficient (N F : ℕ) (η κ delta : ℚ) (S H : ℕ) : ℝ :=
  64 * (F : ℝ) *
    ((4 * (coarseExponent (inputSmallLog N) + 21 : ℕ) * (inputSmallLog N : ℝ)) / (η : ℝ) +
      2 * (κ : ℝ) + (S : ℝ) / (H : ℝ) ^ 3) +
    2 * (delta : ℝ) + 2 * S * (1 / (H : ℝ) ^ 4) * F

section Node

variable {α : Type*} [DecidableEq α]
  (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 1764 ≤ inputSmallLog N)
  {M J P F b Q thetaExponent R H : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (hM : 0 < M) (hMeq : M = (integerParameters N).M)
  (hPeq : P = (integerParameters N).P) (hFeq : F = inputSmallLog N)
  (eb : ℕ) (hbeq : b = 2 ^ eb) (hQeq : Q = inputSmallLog N ^ 80)
  (hthetaeq : thetaExponent = 40 * smallLogExponent N) (hHeq : H = inputHeight N) (hH : 4 ≤ H)
  (U : PhysicalEntry M J target.length → ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta η κ : ℚ)
  (hdelta : 0 < delta) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
  (node : PhysicalInternalNode M J)
  (hleaf : ¬ (physicalSourceInterval source.length node.1).hi -
    (physicalSourceInterval source.length node.1).lo ≤ 1)
  (representative : Fin (stageRepresentatives source target U N P F A node.1).length)
  (scale : Fin (dyadicScales N).length) (hscale : (dyadicScales N).get scale = b)
  (cell : ℕ × ℕ)
  (cellIndex : Fin (physicalProgramCells source target U N P F A thetaExponent node.1
    ((dyadicScales N).get scale)).length)
  (hcell : (physicalProgramCells source target U N P F A thetaExponent node.1
    ((dyadicScales N).get scale)).get cellIndex = cell)
  (hnonempty : physicalNodeCellBands source target U N P F A T node.1 node.2 b thetaExponent
    (rationalParameters F).tau cell ≠ [])
  (specified : UnskippedBand source target (physicalSourceInterval source.length node.1)
    b P thetaExponent (rationalParameters F).tau F
    (physicalBandChildMassTable source target U N P F A T node.1 node.2)
    (physicalBandChildInitial source target U N P F A node.1 node.2))
  (hspecified : specified ∈ physicalNodeCellBands source target U N P F A T node.1 node.2 b thetaExponent
    (rationalParameters F).tau cell)
  (hget : (stageRepresentatives source target U N P F A node.1).get representative = (b, specified.center))
  (q : TargetInterval target.length) (hb : (b : ℝ) ≤ stateEditCost (physicalSource source node.1) target q)
  (hquery : physicalProgramOnlineGuard source target U N P F A node.1 q (b, specified.center))
  (comparison : Fin M → TargetInterval target.length) (hc : comparison ∈ specified.actions)
  (htau : 0 < (rationalParameters F).tau)
  (hηrange : (η : ℝ) * (2 * (delta : ℝ) + 8 * ((128 * F : ℚ) : ℝ) *
    (((2 : ℚ) ^ (-(thetaExponent : ℤ))) : ℝ)) ≤ (κ : ℝ))
  (herror : 2 * (rationalParameters F).gamma +
    512 * (128 * F : ℚ) * F * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ κ * delta)
  (bernstein : ∀ h : Fin (groupDyadicScales M b F).length, FiniteBernsteinInput
    (Measure.pi fun _ : Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F h)) =>
      (PMF.uniformOfFintype (Fin M)).toMeasure))

local notation "tau" => RationalParameters.tau (rationalParameters F)
local notation "onlineKey" => (Sigma.mk node representative : PhysicalOnlineKey source target U N P F A)
local notation "groupKey" => (Sigma.mk node (Sigma.mk scale cellIndex) : PhysicalGroupKey source target U N P F A thetaExponent)
local notation "bandG" => physicalProgramBandG source target U N P F A T thetaExponent H tau node representative
local notation "bandK" => physicalProgramBandK source target U N P F A T thetaExponent H tau node representative
local notation "Draw" => PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau
local notation "Fresh" => PhysicalOnlineArray (R := R) source target U N P F A T thetaExponent H tau onlineKey ×
  PhysicalGroupArray (R := R) source target U N P F A thetaExponent Q groupKey
local notation "choices" => physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ
local notation "refresh" => physicalProgramRefresh source target U N P F A T thetaExponent H Q tau
local notation "localLaw" =>
  Measure.prod (physicalProgramCoordinateLaw (R := R) source target U N P F A T thetaExponent H Q tau (Sum.inl onlineKey))
    (physicalProgramCoordinateLaw (R := R) source target U N P F A T thetaExponent H Q tau (Sum.inr groupKey))
local notation "globalLaw" => physicalProgramDrawLaw (R := R) source target U N P F A T thetaExponent H Q tau

include hN hell hM hMeq hPeq hFeq hbeq hQeq hthetaeq hHeq hH hsize hP hF hA hseed hT
  hdelta hη hκ hκhalf hleaf hscale hcell hnonempty hspecified hget hb hquery hc htau hηrange herror bernstein

/-- The actual program satisfies the fixed-child conditional node bound;
both candidate-list premises and both deeper-agreement premises are proved. -/
theorem physicalProgram_conditional_node_regret (draw : Draw) (S : ℕ) :
    let c : ℝ := stateEditCost (physicalSource source node.1) target q
    let charge : ℝ := ((128 * F : ℚ) : ℝ) * targetEndpointDistance q specified.center
    let clipped := physicalComparisonClipped source target U N P F A T delta (choices draw) node.1 node.2 comparison
    (∫ fresh : Fresh, (∑ t ∈ range S, (max c
      (physicalRefinement source target U N P F A T delta (choices (refresh draw onlineKey groupKey fresh))
        node.1 (t + 1) q : ℝ) - charge - clipped (t + 1))) ∂localLaw) ≤
      ((∑ child, specified.envelope child : ℚ) : ℝ) *
        (Real.log (bandCoordinates specified.actions.toFinset).card / (η : ℝ) + 2 * (κ : ℝ) +
          (S : ℝ) / (H : ℝ) ^ 3) +
        2 * (delta : ℝ) * c + 2 * S * (1 / (H : ℝ) ^ 4) * F * c := by
  have hscalePow : (dyadicScales N).get scale = 2 ^ eb := hscale.trans hbeq
  clear hbeq
  subst b cell
  have hrep : (((dyadicScales N).get scale), specified.center) ∈
      stageRepresentatives source target U N P F A node.1 := by
    simpa only [hget] using List.get_mem (stageRepresentatives source target U N P F A node.1) representative
  have hbound := physical_conditional_node_regret (G := bandG) (K := bandK) source target N hN hell hM hMeq hPeq hFeq
    eb hscalePow hQeq hthetaeq hHeq hH U A hsize hP hF hA hseed T hT delta η κ hdelta hη hκ hκhalf
    (choices draw) node.1 node.2 hleaf
    ((physicalProgramCells source target U N P F A thetaExponent node.1 ((dyadicScales N).get scale)).get cellIndex)
    hnonempty specified hspecified hrep q hb comparison hc
    (physicalProgramBandG_spec source target U N P F A T thetaExponent H tau node representative _ specified hget)
    rfl htau hηrange herror
    (fun fresh => choices (refresh draw onlineKey groupKey fresh))
    (fun fresh label hdeeper =>
      (physicalProgramDrawSelections_refresh_deeper source target U N P F A T thetaExponent H Q tau η κ
        draw onlineKey groupKey fresh label hdeeper hdeeper).1)
    (fun fresh label hdeeper =>
      (physicalProgramDrawSelections_refresh_deeper source target U N P F A T thetaExponent H Q tau η κ
        draw onlineKey groupKey fresh label hdeeper hdeeper).2)
    (fun fresh t => physicalProgramRefresh_online_mem source target U N P F A T thetaExponent H Q tau delta η κ
      node representative scale cellIndex draw fresh specified hget t q hquery)
    (fun fresh t => physicalProgramRefresh_group_mem source target U N P F A T thetaExponent H Q tau delta η κ
      node representative scale cellIndex draw fresh hnonempty t)
    bernstein S
  exact hbound

/-- The actual complete program has the node budget in its original
finite product law. The two selected arrays are independently refreshed,
and all complete child histories stay fixed. -/
theorem physicalProgram_global_node_regret (S : ℕ) :
    let c : ℝ := stateEditCost (physicalSource source node.1) target q
    let charge : ℝ := ((128 * F : ℚ) : ℝ) * targetEndpointDistance q specified.center
    (∫ draw : Draw, (∑ t ∈ range S, (max c
      (physicalRefinement source target U N P F A T delta (choices draw)
        node.1 (t + 1) q : ℝ) - charge -
      physicalComparisonClipped source target U N P F A T delta (choices draw)
        node.1 node.2 comparison (t + 1))) ∂globalLaw) ≤
      physicalProgramNodeCoefficient N F η κ delta S H * c := by
  let c : ℝ := stateEditCost (physicalSource source node.1) target q
  let charge : ℝ := ((128 * F : ℚ) : ℝ) * targetEndpointDistance q specified.center
  let payoff : Draw → ℝ := fun draw => ∑ t ∈ range S,
    (max c (physicalRefinement source target U N P F A T delta (choices draw)
      node.1 (t + 1) q : ℝ) - charge -
      physicalComparisonClipped source target U N P F A T delta (choices draw)
        node.1 node.2 comparison (t + 1))
  change (∫ draw, payoff draw ∂globalLaw) ≤ physicalProgramNodeCoefficient N F η κ delta S H * c
  rw [← physicalProgramDrawLaw_refresh_integral source target U N P F A T thetaExponent H Q tau
    onlineKey groupKey payoff]
  have hlocal (draw : Draw) : (∫ fresh : Fresh, payoff (refresh draw onlineKey groupKey fresh) ∂localLaw) ≤
      physicalProgramNodeCoefficient N F η κ delta S H * c := by
    have hbound := physicalProgram_conditional_node_regret source target N hN hell hM hMeq hPeq hFeq
      eb hbeq hQeq hthetaeq hHeq hH U A hsize hP hF hA hseed T hT delta η κ hdelta hη hκ hκhalf
      node hleaf representative scale hscale cell cellIndex hcell hnonempty specified hspecified hget
      q hb hquery comparison hc htau hηrange herror bernstein draw S
    have hpayoff (fresh : Fresh) : payoff (refresh draw onlineKey groupKey fresh) =
        ∑ t ∈ range S, (max c
          (physicalRefinement source target U N P F A T delta (choices (refresh draw onlineKey groupKey fresh))
            node.1 (t + 1) q : ℝ) - charge -
          physicalComparisonClipped source target U N P F A T delta (choices draw)
            node.1 node.2 comparison (t + 1)) := by
      dsimp only [payoff]
      rw [physicalProgramRefresh_clipped source target U N P F A T thetaExponent H Q tau delta η κ
        node representative scale cellIndex draw fresh comparison]
    simp_rw [hpayoff]
    have hbudget := unskipped_expected_regret_budget source target N hN (by omega : 42 ≤ inputSmallLog N)
      hMeq hPeq (physicalSourceInterval source.length node.1) tau (F : ℚ)
      (physicalBandChildMassTable source target U N P F A T node.1 node.2)
      (physicalBandChildInitial source target U N P F A node.1 node.2)
      specified (Nat.cast_nonneg F) c hb η κ delta hη hκ S H
    apply hbound.trans
    simpa only [physicalProgramNodeCoefficient, Rat.cast_natCast] using hbudget
  have hmean := integral_mono (μ := globalLaw) (.of_finite) (.of_finite) hlocal
  simpa only [integral_const, probReal_univ, one_smul] using hmean

end Node

end EditApproximation

end OAI
