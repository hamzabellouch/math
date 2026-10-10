import OAI.Combinatorics.EditApproximation.Refinement.PhysicalNodeRegret
import OAI.Combinatorics.EditApproximation.Refinement.StageComparisonEnergy

namespace OAI

/-! The generic regret bound for the actual complete physical recurrence. -/

namespace EditApproximation

open Finset

section Node

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A))
  (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (hleaf : ¬ (physicalSourceInterval source.length node).hi -
    (physicalSourceInterval source.length node).lo ≤ 1)
  (q : TargetInterval target.length)
  (hc : 0 < stateEditCost (physicalSource source node) target q)

local notation "parent" => physicalSourceInterval source.length node
local notation "b" => 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
local notation "r" => roundInterval (seedGridSpacing b P) q
local notation "action" => comparisonChildren source target hM P hP parent q hc
local notation "mass" => fun i s => (stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s) : ℝ)
local notation "W" => comparisonActionMass action mass
local notation "value" => fun t (s : PhysicalEntry M J target.length) =>
  (physicalRefinement source target U N P F A T delta choices (Prod.fst s) t (Prod.snd s) : ℝ)
local notation "regret" => fun t =>
  max (stateEditCost (physicalSource source node) target q : ℝ) (value (t + 1) (node, q)) -
    (128 * (F : ℝ)) * targetEndpointDistance q r -
    physicalComparisonClipped source target U N P F A T delta choices node hbelow action (t + 1)

include hsize hF hA hseed hT hleaf in
 theorem physicalNode_generic_regret (S : ℕ) :
    (∑ t ∈ range S, regret t) ≤ W - |stateLengthGap (physicalSource source node) target r| := by
  have hspec := comparisonChildren_spec source target hM P hP parent q hc
  have hzero : endpointActionConnection r action = 0 := hspec.2.1
  have hrep := stageRounded_representative_mem source target U N P F A hsize hP hF hA hseed node q hc
  have hL : (1 : ℝ) ≤ 128 * F := by
    have hFR : (1 : ℝ) ≤ F := by exact_mod_cast hF
    linarith only [hFR]
  have hsplit : (stateEditCost (physicalSource source node) target q : ℝ) ≤
      (128 * (F : ℝ)) * targetEndpointDistance q r +
        ∑ i, (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (action i) : ℝ) := by
    have h := comparisonChildren_lower source target hM P hP parent q hc
    have he := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg (α := ℝ) (targetEndpointDistance q r))
    change (stateEditCost (physicalSource source node) target q : ℝ) ≤
      (∑ i, (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (action i) : ℝ)) +
        targetEndpointDistance q r at h
    simp only [one_mul] at he
    linarith only [h, he]
  have hbellman (t : ℕ) (_ht : t < S) :
      value (t + 1) (node, q) ≤ (128 * (F : ℝ)) * targetEndpointDistance q r +
        ∑ i, value t (physicalChild node hbelow i, action i) := by
    have hQ := (physicalRefinement_bellman_invariants source target U N P F A T delta choices node t q).2
    have hR := (Rat.cast_le (K := ℝ)).mpr hQ
    rw [rationalPhysicalBellman_cast] at hR
    have h := physicalBellman_le_action source target P ((128 * F : ℚ) : ℝ)
      (fun s => (stageInitial source target U N P F A s : ℝ))
      (stageRepresentatives source target U N P F A) (value t) node hbelow hleaf q r b hrep action hspec.1
    rw [hzero, Nat.cast_zero, add_zero] at h
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using hR.trans h
  have hmono (i : Fin M) (_hi : i ∈ (univ : Finset (Fin M))) :
      value S (physicalChild node hbelow i, action i) ≤ value 0 (physicalChild node hbelow i, action i) := by
    apply Rat.cast_le.mpr
    have hantitone : Antitone (fun t => physicalRefinement source target U N P F A T delta choices
        (physicalChild node hbelow i) t (action i)) :=
      antitone_nat_of_succ_le (fun t => physicalRefinement_nonincreasing source target U N P F A T delta choices
        (physicalChild node hbelow i) t (action i))
    exact hantitone (Nat.zero_le S)
  have hinv (i : Fin M) := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed
    T hT (physicalChild node hbelow i, action i)
  have hinit (i : Fin M) (_hi : i ∈ (univ : Finset (Fin M))) :
      value 0 (physicalChild node hbelow i, action i) ≤ mass i (action i) := by
    dsimp only
    rw [physicalRefinement_zero]
    exact Rat.cast_le.mpr (hinv i).2.1
  have hgapMass (i : Fin M) (_hi : i ∈ (univ : Finset (Fin M))) :
      |stateLengthGap (physicalSource source (physicalChild node hbelow i)) target (action i)| ≤ mass i (action i) :=
    ((le_max_right _ _).trans (hinv i).1).trans (Rat.cast_le.mpr (hinv i).2.1)
  have h := generic_regret_mass_bound univ S
    (stateEditCost (physicalSource source node) target q : ℝ)
    ((128 * (F : ℝ)) * targetEndpointDistance q r)
    (fun i => (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (action i) : ℝ))
    (fun i => mass i (action i))
    (fun i => stateLengthGap (physicalSource source (physicalChild node hbelow i)) target (action i))
    (fun t => value t (node, q)) (fun t i => value t (physicalChild node hbelow i, action i))
    hsplit hbellman hmono hinit
    (fun i _ => stateEditCost_length_lower _ _ _) hgapMass
  apply h.trans
  have hsum := sum_mass_sub_abs_le univ (fun i => mass i (action i))
    (fun i => stateLengthGap (physicalSource source (physicalChild node hbelow i)) target (action i))
  have hgapSum : (∑ i, stateLengthGap (physicalSource source (physicalChild node hbelow i)) target (action i)) =
      stateLengthGap (physicalSource source node) target r :=
    zero_connection_gap_sum source target hM parent r action hzero
  rw [hgapSum] at hsum
  exact hsum

include hsize hF hA hseed hT in
 theorem physicalComparison_mass_upper (hMP : 4 * (M : ℝ) / P ≤ 1) :
    W ≤ 4 * F * stateEditCost (physicalSource source node) target q := by
  have hcost := comparisonChildren_cost_bound source target hM P hP parent q hc
  change (∑ i, (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (action i) : ℝ)) ≤
    (1 + 4 * (M : ℝ) / P) * stateEditCost (physicalSource source node) target q at hcost
  have hsum : W ≤ 2 * (F : ℝ) * ∑ i,
      (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (action i) : ℝ) := by
    change (∑ i, mass i (action i)) ≤ _
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    have h := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT
      (physicalChild node hbelow i, action i)
    have hQ := h.2.2.1.trans h.2.2.2
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using (Rat.cast_le (K := ℝ)).mpr hQ
  have hfactor := mul_le_mul_of_nonneg_left hcost (show (0 : ℝ) ≤ 2 * F by positivity)
  have hcost0 : (0 : ℝ) ≤ stateEditCost (physicalSource source node) target q := Nat.cast_nonneg _
  have hfactor2 := mul_le_mul_of_nonneg_right hMP hcost0
  have hfactor3 := mul_le_mul_of_nonneg_left hfactor2 (show (0 : ℝ) ≤ 2 * F by positivity)
  nlinarith only [hsum, hfactor, hfactor3]

include hsize hF hA hseed hT hleaf in
 theorem physicalNode_generic_regret_upper (hMP : 4 * (M : ℝ) / P ≤ 1) (S : ℕ) :
    (∑ t ∈ range S, regret t) ≤ 4 * F * stateEditCost (physicalSource source node) target q := by
  exact (physicalNode_generic_regret source target hM U N P F A hsize hP hF hA hseed T hT delta choices node
    hbelow hleaf q hc S).trans ((sub_le_self _ (abs_nonneg _)).trans
      (physicalComparison_mass_upper source target hM U N P F A hsize hP hF hA hseed T hT node hbelow q hc hMP))

include hsize hF hA hseed hT hleaf in
 theorem physicalNode_near_length_gap_regret
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) (hMP : 4 * (M : ℝ) / P ≤ 1)
    (hnonempty : wideActionList M parent r b P ≠ []) (tau : ℚ) (htau : 0 ≤ tau)
    (hprediction : 1 - tau < |rationalStateGap (physicalSource source node) target r /
      rationalWideActionMinimum parent r b P hnonempty
        (physicalBandChildMassTable source target U N P F A T node hbelow)|)
    (ratio : ℝ)
    (hdiscrepancy : W - wideActionMinimum parent r b P hnonempty mass ≤
      ratio * stateEditCost (physicalSource source node) target q) (S : ℕ) :
    (∑ t ∈ range S, regret t) ≤
      (ratio + 4 * (tau : ℝ) * F) * stateEditCost (physicalSource source node) target q := by
  let Z := wideActionMinimum parent r b P hnonempty mass
  have hspec := comparisonChildren_spec source target hM P hP parent q hc
  have ha : (1 : ℝ) ≤ refinementFactor A F := by
    simpa only [Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr (refinementFactor_spec A F (by omega)).1
  have hlower := wideActionMinimum_lower source target hM parent r b P hnonempty
    (refinementFactor A F : ℝ) ha mass
    (stageWarmupMass_child_lower source target hM U N P F A hsize hP hF hA hseed T hT node hbelow)
  have hpositive := (stageComparison_positive_movement source target hM U N P F A hsize hP hF hA hseed
    T hT node q hc hscale).1
  have hcostPos : (0 : ℝ) < stateEditCost (physicalSource source node) target r := by exact_mod_cast hpositive
  have hZ : 0 < Z := (div_pos hcostPos (by linarith only [ha])).trans_le ((le_max_left _ _).trans hlower)
  have hZW : Z ≤ W := by
    have h := wideActionMinimum_le_member parent r hnonempty mass action hspec.1
    have hzero : endpointActionConnection r action = 0 := hspec.2.1
    simpa only [Z, endpointActionValue, hzero, Nat.cast_zero, zero_add, comparisonActionMass] using h
  have hpred : 1 - (tau : ℝ) < |stateLengthGap (physicalSource source node) target r| / Z := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hprediction
    simp only [Rat.cast_sub, Rat.cast_one, Rat.cast_abs, Rat.cast_div, rationalStateGap_cast,
      rationalWideActionMinimum_cast, abs_div] at h
    change 1 - (tau : ℝ) < |stateLengthGap (physicalSource source node) target r| / |Z| at h
    rwa [abs_of_pos hZ] at h
  have hnear := near_length_gap_regret_bound W Z (stateLengthGap (physicalSource source node) target r)
    (tau : ℝ) ratio F (stateEditCost (physicalSource source node) target q) hZ hZW
    ((Rat.cast_nonneg (K := ℝ)).mpr htau) hpred hdiscrepancy
    (physicalComparison_mass_upper source target hM U N P F A hsize hP hF hA hseed T hT node hbelow q hc hMP)
  exact (physicalNode_generic_regret source target hM U N P F A hsize hP hF hA hseed T hT delta choices
    node hbelow hleaf q hc S).trans hnear

end Node

end EditApproximation

end OAI
