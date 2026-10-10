import OAI.Combinatorics.EditApproximation.Refinement.StageComparison
import OAI.Combinatorics.EditApproximation.Refinement.ComputedComparisonBand

namespace OAI

/-! The actual averaged warmup supplies the local mass and energy charges. -/

namespace EditApproximation

open Finset

theorem stateLengthGap_difference {α : Type*} (source target : List α)
    (q r : TargetInterval target.length) :
    |stateLengthGap source target q - stateLengthGap source target r| ≤
      (targetEndpointDistance q r : ℝ) := by
  have hid : stateLengthGap source target q - stateLengthGap source target r =
      ((q.hi : ℝ) - r.hi) - ((q.lo : ℝ) - r.lo) := by
    unfold stateLengthGap
    ring
  rw [hid]
  have h := abs_sub ((q.hi : ℝ) - r.hi) ((q.lo : ℝ) - r.lo)
  rw [natural_distance_cast, natural_distance_cast] at h
  simpa only [targetEndpointDistance, Nat.cast_add, add_comm] using h

section Stage

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (q : TargetInterval target.length)
  (hc : 0 < stateEditCost (physicalSource source node) target q)

include hM hsize hP hF hA hseed hT hc in
/-- The rounded representative has positive true cost, and its movement is
smaller than the actual parent averaged warmup mass. -/
theorem stageComparison_positive_movement
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) :
    let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
    let r := roundInterval (seedGridSpacing b P) q
    0 < stateEditCost (physicalSource source node) target r ∧
      (targetEndpointDistance q r : ℝ) ≤ stageWarmupMass source target U N P F A T (node, q) := by
  dsimp only
  let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
  let r := roundInterval (seedGridSpacing b P) q
  let c : ℝ := stateEditCost (physicalSource source node) target q
  let e : ℝ := targetEndpointDistance q r
  let a : ℝ := refinementFactor A F
  have ha : 1 ≤ a := by
    dsimp only [a]
    simpa only [Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr (refinementFactor_spec A F (by omega)).1
  have ha0 : 0 < a := by linarith only [ha]
  have hc0 : 0 < c := by dsimp only [c]; exact_mod_cast hc
  have he0 : 0 ≤ e := Nat.cast_nonneg _
  have hb : (b : ℝ) ≤ c := by
    dsimp only [b, c]
    exact_mod_cast (cost_dyadicScale _ _ hc le_rfl).2.1
  have herror : e * (P : ℝ) ≤ 2 * (b : ℝ) := by
    dsimp only [e, r]
    exact_mod_cast rounded_seedGrid_error b P (by omega) q
  have hPfour : (4 : ℝ) ≤ P := by exact_mod_cast (show 4 ≤ P by omega)
  have hmul := mul_le_mul_of_nonneg_left hPfour he0
  have hhalf : e ≤ c / 2 := by nlinarith only [hmul, herror, hb]
  have hspatial : c ≤ stateEditCost (physicalSource source node) target r + e := by
    dsimp only [c, e]
    exact_mod_cast stateEditCost_spatial (physicalSource source node) target q r
  have hsmall : e ≤ c / a := by
    have h := mul_le_mul_of_nonneg_left hscale he0
    apply (le_div_iff₀ ha0).2
    nlinarith only [h, herror, hb]
  have hinv := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT (node, q)
  have hlower : c / a ≤ (stageWarmupMass source target U N P F A T (node, q) : ℝ) :=
    ((le_max_left _ _).trans hinv.1).trans (Rat.cast_le.mpr hinv.2.1)
  exact ⟨by exact_mod_cast (show (0 : ℝ) < stateEditCost (physicalSource source node) target r by linarith),
    hsmall.trans hlower⟩

include hsize hF hA hseed hT in
/-- No local energy or discrepancy hypothesis is assumed: these are the
charges of the input-determined comparison children and the actual warmup. -/
theorem stageComparison_energy
    (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (hscale : 2 * (refinementFactor A F : ℝ) ≤ P) :
    let parent := physicalSourceInterval source.length node
    let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
    let r := roundInterval (seedGridSpacing b P) q
    let action := comparisonChildren source target hM P hP parent q hc
    let child := fun i s => (stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s) : ℝ)
    let mp := (stageWarmupMass source target U N P F A T (node, q) : ℝ)
    let W := comparisonActionMass action child
    let K := comparisonActionCurvature source target parent r action child
    let energy := (stateLengthGap (physicalSource source node) target q) ^ 2 / mp
    ∃ hnonempty : wideActionList M parent r b P ≠ [],
      let Z := wideActionMinimum parent r b P hnonempty child
      0 ≤ K ∧ 0 ≤ W - Z ∧
      mp - W + (W - Z) ≤
        (128 * (F : ℝ)) * targetEndpointDistance q r +
          (stageInitial source target U N P F A (node, q) : ℝ) / T ∧
      K ≤ ((∑ i, (stateLengthGap (physicalSource source (physicalChild node hbelow i)) target
          (action i)) ^ 2 / child i (action i)) - energy) +
        3 * targetEndpointDistance q r + 2 * max (-(mp - W)) 0 := by
  dsimp only
  let parent := physicalSourceInterval source.length node
  let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
  let r := roundInterval (seedGridSpacing b P) q
  let action := comparisonChildren source target hM P hP parent q hc
  let child := fun i s => (stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s) : ℝ)
  let mp := (stageWarmupMass source target U N P F A T (node, q) : ℝ)
  let W := comparisonActionMass action child
  let K := comparisonActionCurvature source target parent r action child
  have hspec := comparisonChildren_spec source target hM P hP parent q hc
  have hzero : endpointActionConnection r action = 0 := hspec.2.1
  have hnonempty : wideActionList M parent r b P ≠ [] := by
    intro heq
    have hmem := hspec.1
    change action ∈ wideActionList M parent r b P at hmem
    rw [heq] at hmem
    exact List.not_mem_nil hmem
  let Z := wideActionMinimum parent r b P hnonempty child
  have ha : (1 : ℝ) ≤ refinementFactor A F := by
    simpa only [Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr (refinementFactor_spec A F (by omega)).1
  have hlower := stageWarmupMass_child_lower source target hM U N P F A hsize hP hF hA hseed T hT node hbelow
  have hZlower := wideActionMinimum_lower source target hM parent r b P hnonempty
    (refinementFactor A F : ℝ) ha child hlower
  have hpositive := stageComparison_positive_movement source target hM U N P F A hsize hP hF hA hseed
    T hT node q hc hscale
  have hcr : (0 : ℝ) < stateEditCost (physicalSource source node) target r := by exact_mod_cast hpositive.1
  have hZpos : 0 < Z := (div_pos hcr (by linarith only [ha])).trans_le ((le_max_left _ _).trans hZlower)
  have hZW : Z ≤ W := by
    have h := wideActionMinimum_le_member parent r hnonempty child action hspec.1
    simpa only [Z, W, comparisonActionMass, endpointActionValue, hzero, Nat.cast_zero, zero_add] using h
  have hWpos : 0 < W := hZpos.trans_le hZW
  have hgap (i : Fin M) : |stateLengthGap (physicalSource source (physicalChild node hbelow i)) target
      (action i)| ≤ child i (action i) := (le_max_right _ _).trans (hlower i (action i))
  have hK := comparisonActionCurvature_nonneg source target hM parent r action child hgap hspec.2.1 hWpos
  have hinv := stageWarmup_invariants source target hM U N P F A hsize hP hF hA hseed T hT (node, q)
  have hparentGap : |stateLengthGap (physicalSource source node) target q| ≤ mp :=
    ((le_max_right _ _).trans hinv.1).trans (Rat.cast_le.mpr hinv.2.1)
  have hmp : 0 < mp := by
    have hcR : (0 : ℝ) < stateEditCost (physicalSource source node) target q := by exact_mod_cast hc
    have h := ((le_max_left _ _).trans hinv.1).trans (Rat.cast_le.mpr hinv.2.1)
    exact (div_pos hcR (by linarith only [ha])).trans_le h
  have hroundedGap : |stateLengthGap (physicalSource source node) target r| ≤ W :=
    ((le_max_right _ _).trans hZlower).trans hZW
  have henergy := local_energy_discrepancy hmp hWpos hparentGap hroundedGap
    (stateLengthGap_difference (physicalSource source node) target q r) hpositive.2
  have hslack := stageWarmup_comparison_slack source target hM U N P F A hsize hP hF hA hseed
    T hT node hbelow hleaf q hc hnonempty
  refine ⟨hnonempty, hK, sub_nonneg.mpr hZW, ?_, ?_⟩
  · change mp - W + (W - Z) ≤ _
    change mp - Z ≤ _ at hslack
    linarith only [hslack]
  · let Echild := ∑ i, (stateLengthGap (physicalSource source (physicalChild node hbelow i)) target
        (action i)) ^ 2 / child i (action i)
    change Echild - (stateLengthGap (physicalSource source node) target r) ^ 2 / W ≤
      (Echild - (stateLengthGap (physicalSource source node) target q) ^ 2 / mp) +
        3 * (targetEndpointDistance q r : ℝ) + 2 * max (-(mp - W)) 0
    have hid : -(mp - W) = W - mp := by ring
    rw [hid]
    linarith only [henergy]

end Stage

end EditApproximation

end OAI
