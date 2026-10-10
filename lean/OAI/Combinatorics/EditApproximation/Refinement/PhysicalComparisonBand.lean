import OAI.Combinatorics.EditApproximation.Refinement.PhysicalUnskippedComparison
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalNodeRegret
import OAI.Combinatorics.EditApproximation.Refinement.StageComparisonEnergy
import OAI.Combinatorics.EditApproximation.Refinement.ComputedBandSpacing

namespace OAI

/-! Non-bad, low-velocity comparison children belong to an actual unskipped cell band. -/

namespace EditApproximation

open Finset

section Node

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P : ℕ) (A : ℚ)
  (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
  (hMeq : M = (integerParameters N).M) (hPeq : P = (integerParameters N).P)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (q : TargetInterval target.length) (hc : 0 < stateEditCost (physicalSource source node) target q)

local notation "F" => inputSmallLog N
local notation "parent" => physicalSourceInterval source.length node
local notation "b" => (2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q) : ℕ)
local notation "r" => roundInterval (seedGridSpacing b P) q
local notation "action" => comparisonChildren source target hM P hP parent q hc
local notation "child" => physicalBandChildMassTable source target U N P F A T node hbelow
local notation "childR" => fun i s => (child i s : ℝ)
local notation "initial" => physicalBandChildInitial source target U N P F A node hbelow
local notation "tau" => RationalParameters.tau (rationalParameters (inputSmallLog N))
local notation "theta" => RationalParameters.theta (rationalParameters (inputSmallLog N))
local notation "thetaExponent" => 40 * smallLogExponent N

include hN hell hMeq hPeq hsize hA hseed hT in
 theorem physicalComparison_unskipped
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hnonempty : wideActionList M parent r b P ≠ [])
    (hvelocity : |rationalStateGap (physicalSource source node) target r /
      rationalWideActionMinimum parent r b P hnonempty child| ≤ 1 - tau)
    (hKsmall : comparisonActionCurvature source target parent r action childR ≤ b / heightQuarterRoot N)
    (hGsmall : comparisonActionMass action childR - wideActionMinimum parent r b P hnonempty childR ≤
      b / heightQuarterRoot N) :
    ∃ member : UnskippedBand source target parent b P thetaExponent tau F child initial,
      member ∈ physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau
        (targetCell (theta * b) r) ∧ member.center = r ∧ action ∈ member.actions := by
  have hF : 1 ≤ F := Nat.one_le_two_pow
  have hell2 : 2 ≤ F := by
    have h : 2 ≤ (2 : ℕ) ^ 1000 := by
      simpa only [pow_one] using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 1 ≤ 1000)
    exact h.trans hell
  have hspec := comparisonChildren_spec source target hM P hP parent q hc
  have hrep := stageRounded_representative_mem source target U N P F A hsize hP hF hA hseed node q hc
  have hdyadic := cost_dyadicScale _ _ hc le_rfl
  have hcR : (stateEditCost (physicalSource source node) target q : ℝ) ≤ 2 * (b : ℝ) := by
    exact_mod_cast hdyadic.2.2.le
  have hcost := comparisonChildren_cost_bound source target hM P hP parent q hc
  change (∑ i, (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (action i) : ℝ)) ≤
    (1 + 4 * (M : ℝ) / P) * stateEditCost (physicalSource source node) target q at hcost
  have hcostSum : (∑ i, (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (action i) : ℝ)) ≤
      4 * b := by
    have h := mul_le_mul_of_nonneg_right hMP
      (Nat.cast_nonneg (α := ℝ) (stateEditCost (physicalSource source node) target q))
    nlinarith only [hcost, hcR, h]
  have ha : (1 : ℝ) ≤ refinementFactor A F := by
    simpa only [Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr (refinementFactor_spec A F (by omega)).1
  have hlower := stageWarmupMass_child_lower source target hM U N P F A hsize hP hF hA hseed T hT node hbelow
  have hupper (i : Fin M) : (child i (action i) : ℝ) ≤
      2 * F * stateEditCost (physicalSource source (physicalChild node hbelow i)) target (action i) := by
    dsimp only [physicalBandChildMassTable]
    have h := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT
      (physicalChild node hbelow i, action i)
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
      (Rat.cast_le (K := ℝ)).mpr (h.2.2.1.trans h.2.2.2)
  have hpositive := (stageComparison_positive_movement source target hM U N P F A hsize hP hF hA hseed
    T hT node q hc hscale).1
  have hband := computed_comparison_band_mem source target N hN hell hM hMeq parent r action
    hspec.1 hnonempty child (refinementFactor A F : ℝ) ha hlower hupper hcostSum hpositive
    hspec.2.1 hspec.2.2.2.1 hvelocity hKsmall hGsmall
  have hnum := computed_band_basic_constants N hell2
  have hspacing := computed_band_spacing_dominates N hN hell
  rw [← hMeq, ← hPeq, computed_theta_dyadic] at hspacing
  rw [computed_theta_dyadic] at hnum
  have hmember := physical_comparison_unskipped source target hM U N P F A hsize hP hF hA hseed
    T node hbelow b thetaExponent (Nat.two_pow_pos _) ⟨_, rfl⟩
    ⟨_, hPeq.trans (computed_P_dyadic N)⟩ tau hnum.1 hnum.2.2.1 hnum.2.2.2.1 hnum.2.2.2.2 hspacing
    r hrep action (by simpa only [← computed_theta_dyadic, physicalSource] using hband)
    (by exact_mod_cast hcostSum)
  simpa only [physicalNodeCellBands, computed_theta_dyadic] using hmember

end Node

end EditApproximation

end OAI
