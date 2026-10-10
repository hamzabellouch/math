import OAI.Combinatorics.EditApproximation.Refinement.PhysicalOnlineBand
import OAI.Combinatorics.EditApproximation.Geometry.CellGroupSelection
import OAI.Combinatorics.EditApproximation.Probability.ExpectedRegret
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# First crossing for the literal physical refinement

Online and selected-group candidates are connected to the complete
refinement by membership in its actual finite lists. Group success is the
literal simultaneous estimator-error test, rather than a cone-bound
assumption. The child environment remains fixed throughout this argument.
-/

namespace EditApproximation

open Finset



theorem representativeBandActions_zero_connection {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P : ℕ) (tau theta : ℚ) (child : Fin M → TargetInterval target.length → ℚ)
    (action : Fin M → TargetInterval target.length)
    (haction : action ∈ representativeBandActions source target parent r b P tau theta child) :
    endpointActionConnection r action = 0 := by
  by_cases hwide : wideActionList M parent r b P = []
  · simp only [representativeBandActions, dite_eq_left hwide, List.not_mem_nil] at haction
  · by_cases hZ : 0 < rationalWideActionMinimum parent r b P hwide child
    · simp only [representativeBandActions, dite_eq_right hwide, ite_eq_left hZ] at haction
      exact (computedBandActions_mem parent r b P tau theta _ child action haction).choose_spec.2.2.1
    · simp only [representativeBandActions, dite_eq_right hwide, ite_eq_right hZ, List.not_mem_nil] at haction

theorem sharedBandRationalAction_wide {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (representatives : List (ℕ × TargetInterval target.length)) (b P : ℕ) (tau theta : ℚ)
    (child : Fin M → TargetInterval target.length → ℚ) (hrep : (b, r) ∈ representatives)
    (action : Fin M → TargetInterval target.length)
    (haction : action ∈ representativeBandActions source target parent r b P tau theta child) :
    sharedBandRationalAction r action ∈ rationalActualWideActions parent representatives P := by
  apply List.mem_flatMap.mpr
  refine ⟨(b, r), hrep, List.mem_map.mpr ⟨action,
    representativeBandActions_wide source target parent r b P tau theta child action haction, ?_⟩⟩
  simp only [sharedBandRationalAction,
    representativeBandActions_zero_connection source target parent r b P tau theta child action haction,
    Nat.cast_zero]

theorem rationalOnlineMinimum_le_member (values : List ℚ) (value : ℚ) (hvalue : value ∈ values) :
    ∃ online, rationalOnlineMinimum values = some online ∧ online ≤ value := by
  cases values with
  | nil => simp only [List.not_mem_nil] at hvalue
  | cons first rest =>
    refine ⟨rationalMinimum first rest, rfl, ?_⟩
    rcases List.mem_cons.mp hvalue with rfl | hrest
    · exact rationalMinimum_le_fallback _ _
    · exact rationalMinimum_le_member _ _ hrest

theorem rationalWideStep_online_exists {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (initial : TargetInterval ny → ℚ) (L delta : ℚ)
    (old current : Fin M × TargetInterval ny → ℚ)
    (groups online : List (PhysicalRationalAction M ny)) (q : TargetInterval ny)
    (action : PhysicalRationalAction M ny) (haction : action ∈ online) :
    ∃ value, rationalOnlineMinimum
        (online.map (rationalActionValue (fun q r => targetEndpointDistance q r) L current q)) = some value ∧
      value ≤ rationalActionValue (fun q r => targetEndpointDistance q r) L current q action ∧
      (rationalWideStep parent representatives P initial L delta old current groups online q : ℝ) =
        refinementUpdate (delta : ℝ)
          (rationalWideStepCone parent representatives P initial L old current groups q : ℝ) (value : ℝ) := by
  obtain ⟨value, hvalue, hle⟩ := rationalOnlineMinimum_le_member _ _
    (List.mem_map.mpr ⟨action, haction, rfl⟩)
  refine ⟨value, hvalue, hle, ?_⟩
  rw [rationalWideStep, hvalue, rationalRefinementUpdate_cast]

theorem rationalWideStepCone_le_group {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (initial : TargetInterval ny → ℚ) (L : ℚ)
    (old current : Fin M × TargetInterval ny → ℚ)
    (groups : List (PhysicalRationalAction M ny)) (q : TargetInterval ny)
    (action : PhysicalRationalAction M ny) (haction : action ∈ groups) :
    rationalWideStepCone parent representatives P initial L old current groups q ≤
      rationalActionValue (fun q r => targetEndpointDistance q r) L current q action :=
  rationalMinimum_le_member _ _ (List.mem_map.mpr ⟨action, haction, rfl⟩)

theorem rationalWideStepCone_le_wide {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (initial : TargetInterval ny → ℚ) (L : ℚ)
    (old current : Fin M × TargetInterval ny → ℚ)
    (groups : List (PhysicalRationalAction M ny)) (q : TargetInterval ny)
    (action : PhysicalRationalAction M ny)
    (haction : action ∈ rationalActualWideActions parent representatives P) :
    rationalWideStepCone parent representatives P initial L old current groups q ≤
      rationalActionValue (fun q r => targetEndpointDistance q r) L old q action :=
  (rationalMinimum_le_fallback _ _).trans (rationalBellman_le_action _ _ _ _ _ _ action haction)

/-- The actual per-group failure test uses the rational estimated costs. -/
def unskippedGroupFailure {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P thetaExponent : ℕ) (tau F : ℚ)
    (child initial value : Fin M → TargetInterval target.length → ℚ) (Q : ℕ)
    (members : List (UnskippedBand source target parent b P thetaExponent tau F child initial))
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (gamma : ℚ) : Bool :=
  members.any fun member => decide (gamma * b <
    |dyadicUnskippedGroupEstimate Q value member draw -
      rationalEndpointActionValue member.center member.rounded value|)

theorem unskippedGroupFailure_false {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P thetaExponent : ℕ) (tau F : ℚ)
    (child initial value : Fin M → TargetInterval target.length → ℚ) (Q : ℕ)
    (members : List (UnskippedBand source target parent b P thetaExponent tau F child initial))
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (gamma : ℚ) (hfailure : unskippedGroupFailure source target parent b P thetaExponent tau F
      child initial value Q members draw gamma = false) :
    ∀ member ∈ members, |dyadicUnskippedGroupEstimate Q value member draw -
      rationalEndpointActionValue member.center member.rounded value| ≤ gamma * b := by
  intro member hmember
  by_contra hnot
  have hlt := lt_of_not_ge hnot
  have htrue : unskippedGroupFailure source target parent b P thetaExponent tau F
      child initial value Q members draw gamma = true := by
    exact List.any_eq_true.mpr ⟨member, hmember, by simp only [hlt, decide_true]⟩
  rw [hfailure] at htrue
  cases htrue

/-- A selected group candidate in the actual list supplies the cone bound
on the literal estimator-success event. -/
theorem rationalWideStepCone_group_bound {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (representatives : List (ℕ × TargetInterval target.length))
    (b P F thetaExponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (old current : Fin M × TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (hnonempty : cellUnskippedBands source target parent b P F thetaExponent tau a
      parentInitial child initial cell ≠ [])
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (specified : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (hspecified : specified ∈ cellUnskippedBands source target parent b P F thetaExponent tau a
      parentInitial child initial cell)
    (groups : List (PhysicalRationalAction M target.length))
    (hselected : (chooseUnskippedGroup Q (fun i s => current (i, s))
      (cellUnskippedBands source target parent b P F thetaExponent tau a parentInitial child initial cell)
      hnonempty draw).rationalAction ∈ groups)
    (delta L gamma : ℚ) (hF : 1 ≤ F) (hL : 2 ≤ L) (htau : 0 < tau)
    (hspatial : ∀ i s t, current (i, s) ≤ (1 + delta) * current (i, t) + L * targetEndpointDistance s t)
    (hfailure : unskippedGroupFailure source target parent b P thetaExponent tau F child initial
      (fun i s => current (i, s)) Q
      (cellUnskippedBands source target parent b P F thetaExponent tau a parentInitial child initial cell)
      draw gamma = false)
    (action : Fin M → TargetInterval target.length) (haction : action ∈ specified.actions)
    (q : TargetInterval target.length) :
    rationalWideStepCone parent representatives P parentInitial L old current groups q ≤
      L * targetEndpointDistance q specified.center + (1 + delta) * (∑ i, current (i, action i)) +
        (2 * gamma + 512 * L * F * (2 : ℚ) ^ (-(thetaExponent : ℤ))) * b := by
  have haccurate := unskippedGroupFailure_false source target parent b P thetaExponent tau F child initial
    (fun i s => current (i, s)) Q _ draw gamma hfailure
  exact (rationalWideStepCone_le_group parent representatives P parentInitial L old current groups q _ hselected).trans
    (chooseCellGroup_cone_bound source target parent b P F thetaExponent Q tau a parentInitial child initial
      (fun i s => current (i, s)) cell hnonempty draw specified hspecified delta L gamma hF hL htau
      hspatial haccurate action haction q)


section PhysicalNode

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A))
  (node : PhysicalNode M J) (hbelow : node.1.val < J)

def physicalNodeChildren : PhysicalChildTables M target.length := fun i =>
  physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow i)

def physicalNodeGroups (t : ℕ) : List (PhysicalRationalAction M target.length) :=
  choices.groups node (physicalNodeChildren source target U N P F A T delta choices node hbelow) (t + 1)

def physicalNodeOnline (t : ℕ) (q : TargetInterval target.length) : List (PhysicalRationalAction M target.length) :=
  choices.online node (physicalNodeChildren source target U N P F A T delta choices node hbelow) (t + 1) q

def physicalNodeCone (t : ℕ) (q : TargetInterval target.length) : ℚ :=
  rationalWideStepCone (physicalSourceInterval source.length node)
    (stageRepresentatives source target U N P F A node) P
    (fun r => stageInitial source target U N P F A (node, r)) (128 * F)
    (physicalBandHistory source target U N P F A T delta choices node hbelow t)
    (physicalBandHistory source target U N P F A T delta choices node hbelow (t + 1))
    (physicalNodeGroups source target U N P F A T delta choices node hbelow t) q

def physicalNodeOnlineValue (t : ℕ) (q : TargetInterval target.length) : ℚ :=
  (rationalOnlineMinimum ((physicalNodeOnline source target U N P F A T delta choices node hbelow t q).map
    (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
      (physicalBandHistory source target U N P F A T delta choices node hbelow (t + 1)) q))).getD 0

local notation "history" => physicalBandHistory source target U N P F A T delta choices node hbelow
local notation "groups" => physicalNodeGroups source target U N P F A T delta choices node hbelow
local notation "online" => physicalNodeOnline source target U N P F A T delta choices node hbelow
local notation "cone" => physicalNodeCone source target U N P F A T delta choices node hbelow
local notation "onlineValue" => physicalNodeOnlineValue source target U N P F A T delta choices node hbelow
local notation "parent" => physicalSourceInterval source.length node
local notation "representatives" => stageRepresentatives source target U N P F A node
local notation "initialParent" => fun r => stageInitial source target U N P F A (node, r)
local notation "L" => (128 * F : ℚ)

/-- Literal candidate membership makes the online option present. -/
theorem physicalNode_next_eq (hleaf : ¬ (parent).hi - (parent).lo ≤ 1)
    (t : ℕ) (q : TargetInterval target.length) (action : PhysicalRationalAction M target.length)
    (haction : action ∈ online t q) :
    (physicalRefinement source target U N P F A T delta choices node (t + 1) q : ℝ) =
      refinementUpdate (delta : ℝ) (cone t q : ℝ) (onlineValue t q : ℝ) := by
  obtain ⟨value, hvalue, _, hstep⟩ := rationalWideStep_online_exists parent representatives P initialParent L delta
    (history t) (history (t + 1)) (groups t) (online t q) q action haction
  rw [physicalRefinement_succ source target U N P F A T delta choices node hbelow hleaf]
  change (rationalWideStep parent representatives P initialParent L delta
      (history t) (history (t + 1)) (groups t) (online t q) q : ℝ) = _
  rw [hstep]
  congr 1
  simp only [physicalNodeOnlineValue, hvalue, Option.getD_some]

/-- The actual online minimum is at most any listed shared band action. -/
theorem physicalNode_online_le (t : ℕ) (q r : TargetInterval target.length)
    (action : Fin M → TargetInterval target.length)
    (haction : sharedBandRationalAction r action ∈ online t q) :
    (onlineValue t q : ℝ) ≤ (L : ℝ) * targetEndpointDistance q r +
      ∑ i, (history (t + 1) (i, action i) : ℝ) := by
  obtain ⟨value, hvalue, hle⟩ := rationalOnlineMinimum_le_member
    ((online t q).map (rationalActionValue (fun q r => targetEndpointDistance q r) L (history (t + 1)) q))
    (rationalActionValue (fun q r => targetEndpointDistance q r) L (history (t + 1)) q
      (sharedBandRationalAction r action))
    (List.mem_map.mpr ⟨sharedBandRationalAction r action, haction, rfl⟩)
  have hvalueEq : onlineValue t q = value := by
    simp only [physicalNodeOnlineValue, hvalue, Option.getD_some]
  rw [hvalueEq]
  simpa only [rationalActionValue, sharedBandRationalAction, Rat.cast_add, Rat.cast_mul,
    Rat.cast_sum, Rat.cast_natCast, Rat.cast_zero, add_zero] using (Rat.cast_le (K := ℝ)).mpr hle

/-- The old-index wide candidate remains one of the literal cone options. -/
theorem physicalNode_cone_le_old (b : ℕ) (tau theta : ℚ) (r q : TargetInterval target.length)
    (child : Fin M → TargetInterval target.length → ℚ) (hrep : (b, r) ∈ representatives)
    (action : Fin M → TargetInterval target.length)
    (haction : action ∈ representativeBandActions source target parent r b P tau theta child) (t : ℕ) :
    (cone t q : ℝ) ≤ (L : ℝ) * targetEndpointDistance q r + ∑ i, (history t (i, action i) : ℝ) := by
  have hwide := sharedBandRationalAction_wide source target parent r representatives b P tau theta
    child hrep action haction
  have hcone := rationalWideStepCone_le_wide parent representatives P initialParent L
    (history t) (history (t + 1)) (groups t) q _ hwide
  simpa only [physicalNodeCone, rationalActionValue, sharedBandRationalAction,
    Rat.cast_add, Rat.cast_mul, Rat.cast_sum, Rat.cast_natCast, Rat.cast_zero, add_zero] using
    (Rat.cast_le (K := ℝ)).mpr hcone

/-- True cost is bounded by the actual connection charge and clipped
comparison children; no assumption about clipped warmup masses is needed. -/
theorem physicalNode_comparison_lower (hM : 0 < M) (hF : 1 ≤ F)
    (b : ℕ) (tau theta : ℚ) (r q : TargetInterval target.length)
    (child : Fin M → TargetInterval target.length → ℚ)
    (comparison : Fin M → TargetInterval target.length)
    (hc : comparison ∈ representativeBandActions source target parent r b P tau theta child) (t : ℕ) :
    (stateEditCost (physicalSource source node) target q : ℝ) ≤
      (L : ℝ) * targetEndpointDistance q r + ∑ i,
        max (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (comparison i) : ℝ)
          (history t (i, comparison i) : ℝ) := by
  have hzero := representativeBandActions_zero_connection source target parent r b P tau theta child comparison hc
  have hsplit := zero_connection_cost_sum_lower source target hM parent r comparison hzero
  have hspatial : (stateEditCost (physicalSource source node) target q : ℝ) ≤
      stateEditCost (physicalSource source node) target r + (targetEndpointDistance q r : ℝ) := by
    exact_mod_cast stateEditCost_spatial (physicalSource source node) target q r
  have hsum : (∑ i, (stateEditCost
      (physicalSource source (physicalChild node hbelow i)) target (comparison i) : ℝ)) ≤
      ∑ i, max (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (comparison i) : ℝ)
        (history t (i, comparison i) : ℝ) := sum_le_sum fun i _ => le_max_left _ _
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by
    have hFQ : (1 : ℚ) ≤ F := by exact_mod_cast hF
    simpa only [Rat.cast_one] using
      (Rat.cast_le (K := ℝ)).mpr (by linarith only [hFQ] : (1 : ℚ) ≤ L)
  have hcharge := mul_le_mul_of_nonneg_right hLR (Nat.cast_nonneg (α := ℝ) (targetEndpointDistance q r))
  change (stateEditCost (physicalSource source node) target r : ℝ) ≤
    ∑ i, (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (comparison i) : ℝ) at hsplit
  linarith only [hsplit, hspatial, hsum, hcharge]


noncomputable def physicalComparisonClipped
    (comparison : Fin M → TargetInterval target.length) (t : ℕ) : ℝ :=
  ∑ i, max (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (comparison i) : ℝ)
    (history t (i, comparison i) : ℝ)

def physicalNodeCellBands (b thetaExponent : ℕ) (tau : ℚ) (cell : ℕ × ℕ) :=
  cellUnskippedBands source target parent b P F thetaExponent tau (refinementFactor A F)
    initialParent (physicalBandChildMassTable source target U N P F A T node hbelow)
    (physicalBandChildInitial source target U N P F A node hbelow) cell

def physicalNodeSelectedGroup (b thetaExponent Q : ℕ) (tau : ℚ) (cell : ℕ × ℕ)
    (hnonempty : physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell ≠ [])
    (t : ℕ) (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M) :=
  chooseUnskippedGroup Q (fun i s => history (t + 1) (i, s))
    (physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell) hnonempty draw

def physicalNodeGroupFailure (b thetaExponent Q : ℕ) (tau : ℚ) (cell : ℕ × ℕ)
    (t : ℕ) (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M) (gamma : ℚ) : Bool :=
  unskippedGroupFailure source target parent b P thetaExponent tau F
    (physicalBandChildMassTable source target U N P F A T node hbelow)
    (physicalBandChildInitial source target U N P F A node hbelow)
    (fun i s => history (t + 1) (i, s)) Q
    (physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell) draw gamma

variable (hM : 0 < M) (hsize : source.length + target.length ≤ N)
  (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (hT : 0 < T)

include hM hsize hP hF hA hseed hT in
/-- The selected whole-cell representative supplies the actual physical
cone inequality on the actual estimator-success event. -/
theorem physicalNode_group_bound (b thetaExponent Q : ℕ) (tau gamma : ℚ)
    (htau : 0 < tau) (hdelta : 0 ≤ delta) (cell : ℕ × ℕ)
    (hnonempty : physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell ≠ [])
    (specified : UnskippedBand source target parent b P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node hbelow)
      (physicalBandChildInitial source target U N P F A node hbelow))
    (hspecified : specified ∈ physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell)
    (t : ℕ) (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (hselected : (physicalNodeSelectedGroup source target U N P F A T delta choices node hbelow
      b thetaExponent Q tau cell hnonempty t draw).rationalAction ∈ groups t)
    (hfailure : physicalNodeGroupFailure source target U N P F A T delta choices node hbelow
      b thetaExponent Q tau cell t draw gamma = false)
    (action : Fin M → TargetInterval target.length) (haction : action ∈ specified.actions)
    (q : TargetInterval target.length) :
    (cone t q : ℝ) ≤ (1 + (delta : ℝ)) *
        ((L : ℝ) * targetEndpointDistance q specified.center + ∑ i, (history (t + 1) (i, action i) : ℝ)) +
      ((2 * gamma + 512 * L * F * (2 : ℚ) ^ (-(thetaExponent : ℤ)) : ℚ) : ℝ) * b := by
  have hLR : (2 : ℚ) ≤ L := by
    have hFQ : (1 : ℚ) ≤ F := by exact_mod_cast hF
    linarith only [hFQ]
  have hgroup := rationalWideStepCone_group_bound source target parent representatives b P F thetaExponent Q tau
    (refinementFactor A F) initialParent
    (physicalBandChildMassTable source target U N P F A T node hbelow)
    (physicalBandChildInitial source target U N P F A node hbelow)
    (history t) (history (t + 1)) cell hnonempty draw specified hspecified (groups t) hselected
    delta L gamma hF hLR htau
    (fun i s s' => physicalRefinement_spatial source target hM U N P F A hsize hP hF hA hseed
      T hT delta hdelta choices (physicalChild node hbelow i) (t + 1) s s')
    hfailure action haction q
  have hcharge : (0 : ℚ) ≤ L * targetEndpointDistance q specified.center :=
    mul_nonneg (by linarith only [hLR]) (Nat.cast_nonneg _)
  have hslack := mul_nonneg hdelta hcharge
  have hbound : cone t q ≤ (1 + delta) *
      (L * targetEndpointDistance q specified.center + ∑ i, history (t + 1) (i, action i)) +
      (2 * gamma + 512 * L * F * (2 : ℚ) ^ (-(thetaExponent : ℤ))) * b := by
    change cone t q ≤ _ at hgroup
    nlinarith only [hgroup, hslack]
  exact_mod_cast hbound


include hM hsize hP hF hA hseed hT in
 theorem physicalNode_clipped_upper (t : ℕ) (q : TargetInterval target.length) :
    max (stateEditCost (physicalSource source node) target q : ℝ)
      (physicalRefinement source target U N P F A T delta choices node t q : ℝ) ≤
        2 * (F : ℝ) * stateEditCost (physicalSource source node) target q := by
  have hstage := physicalRefinement_stage_bounds source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices node t q
  have hupperQ := (hstage.2.1.trans (hstage.2.2.1.trans hstage.2.2.2.1)).trans hstage.2.2.2.2
  have hupper : (physicalRefinement source target U N P F A T delta choices node t q : ℝ) ≤
      2 * (F : ℝ) * stateEditCost (physicalSource source node) target q := by exact_mod_cast hupperQ
  have hFR : (1 : ℝ) ≤ F := by exact_mod_cast hF
  have hc : (0 : ℝ) ≤ stateEditCost (physicalSource source node) target q := Nat.cast_nonneg _
  exact max_le (by nlinarith only [hFR, hc]) hupper

include hM hsize hP hF hA hseed hT in
/-- Deterministic first-crossing transfer for the complete physical
recurrence, using its actual sampled candidate lists and group-error test. -/
theorem physicalNode_firstCrossing_regret
    (hleaf : ¬ (parent).hi - (parent).lo ≤ 1)
    (b thetaExponent Q : ℕ) (tau gamma κ : ℚ) (htau : 0 < tau)
    (hdelta : 0 < delta) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (cell : ℕ × ℕ)
    (hnonempty : physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell ≠ [])
    (specified : UnskippedBand source target parent b P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node hbelow)
      (physicalBandChildInitial source target U N P F A node hbelow))
    (hspecified : specified ∈ physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell)
    (hrep : (b, specified.center) ∈ representatives)
    (q : TargetInterval target.length)
    (hb : (b : ℝ) ≤ stateEditCost (physicalSource source node) target q)
    (comparison : Fin M → TargetInterval target.length) (hc : comparison ∈ specified.actions)
    (sample : ℕ → Fin M → TargetInterval target.length) (hsample : ∀ t, sample t ∈ specified.actions)
    (draw : ℕ → ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (honline : ∀ t, sharedBandRationalAction specified.center (sample t) ∈ online t q)
    (hselected : ∀ t, (physicalNodeSelectedGroup source target U N P F A T delta choices node hbelow
      b thetaExponent Q tau cell hnonempty t (draw t)).rationalAction ∈ groups t)
    (herror : 2 * gamma + 512 * L * F * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ κ * delta)
    (S : ℕ) :
    let c : ℝ := stateEditCost (physicalSource source node) target q
    let charge : ℝ := (L : ℝ) * targetEndpointDistance q specified.center
    let clipped := physicalComparisonClipped source target U N P F A T delta choices node hbelow comparison
    let failure := fun t => physicalNodeGroupFailure source target U N P F A T delta choices node hbelow
      b thetaExponent Q tau cell t (draw t) gamma
    let crossing := firstCrossing specified.actions.toFinset S
      (fun t => bandActionCost charge (fun t coordinate => (history t coordinate : ℝ)) (t + 1)) c
    (∑ t ∈ range S,
      (max c (physicalRefinement source target U N P F A T delta choices node (t + 1) q : ℝ) -
        charge - clipped (t + 1))) ≤
      (∑ t ∈ range crossing, sampledPrefixRegret charge (κ : ℝ)
        (fun t coordinate => (history t coordinate : ℝ)) clipped sample t) +
          2 * (delta : ℝ) * c + 2 * (F : ℝ) * c *
            ∑ t ∈ range S, (if failure t then (1 : ℝ) else 0) := by
  let c : ℝ := stateEditCost (physicalSource source node) target q
  let charge : ℝ := (L : ℝ) * targetEndpointDistance q specified.center
  let table := fun t coordinate => (history t coordinate : ℝ)
  let clipped := physicalComparisonClipped source target U N P F A T delta choices node hbelow comparison
  let failure := fun t => physicalNodeGroupFailure source target U N P F A T delta choices node hbelow
    b thetaExponent Q tau cell t (draw t) gamma
  let error : ℚ := 2 * gamma + 512 * L * F * (2 : ℚ) ^ (-(thetaExponent : ℤ))
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hFR : (1 : ℝ) ≤ F := by exact_mod_cast hF
  have hδR : (0 : ℝ) < delta := (Rat.cast_pos (K := ℝ)).mpr hdelta
  have hκR : (0 : ℝ) ≤ κ := (Rat.cast_nonneg (K := ℝ)).mpr hκ
  have hκone : (κ : ℝ) ≤ 1 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hκhalf
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
    linarith only [h]
  have herrorQ : error ≤ κ * delta := herror
  have herrorR : (error : ℝ) ≤ (κ : ℝ) * delta := by
    simpa only [Rat.cast_mul] using (Rat.cast_le (K := ℝ)).mpr herrorQ
  have herrorScaled := mul_le_mul_of_nonneg_right herrorR (Nat.cast_nonneg (α := ℝ) b)
  have hκδ := mul_le_mul_of_nonneg_right hκone hδR.le
  have hκδb := mul_le_mul_of_nonneg_right hκδ (Nat.cast_nonneg (α := ℝ) b)
  have hδbc := mul_le_mul_of_nonneg_left hb hδR.le
  have herrorCross : (error : ℝ) * b ≤ (delta : ℝ) * c := by
    nlinarith only [herrorScaled, hκδb, hδbc]
  have hnext (t : ℕ) := physicalNode_next_eq source target U N P F A T delta choices node hbelow
    hleaf t q _ (honline t)
  dsimp only
  simp_rw [hnext]
  apply refinement_firstCrossing_regret specified.actions.toFinset S table clipped sample
    (fun t => (cone t q : ℝ)) (fun t => (onlineValue t q : ℝ)) failure charge c b F delta κ error
    hc0 hFR hδR hκR hb herrorScaled herrorCross
  · intro action _
    apply antitone_nat_of_succ_le
    intro t
    unfold bandActionCost
    apply add_le_add le_rfl
    apply sum_le_sum
    intro i _
    exact (Rat.cast_le (K := ℝ)).mpr
      (physicalBandHistory_nonincreasing source target U N P F A T delta choices node hbelow t (i, action i))
  · intro t _
    exact List.mem_toFinset.mpr (hsample t)
  · intro t _
    exact physicalNode_comparison_lower source target U N P F A T delta choices node hbelow hM hF
      b tau ((2 : ℚ) ^ (-(thetaExponent : ℤ))) specified.center q
      (physicalBandChildMassTable source target U N P F A T node hbelow) comparison hc t
  · intro t _
    exact physicalNode_online_le source target U N P F A T delta choices node hbelow t q specified.center
      (sample t) (honline t)
  · intro t _ action ha
    exact physicalNode_cone_le_old source target U N P F A T delta choices node hbelow
      b tau ((2 : ℚ) ^ (-(thetaExponent : ℤ))) specified.center q
      (physicalBandChildMassTable source target U N P F A T node hbelow) hrep action
      (List.mem_toFinset.mp ha) t
  · intro t _ hf action ha
    exact physicalNode_group_bound source target U N P F A T delta choices node hbelow hM hsize hP hF hA hseed hT
      b thetaExponent Q tau gamma htau hdelta.le cell hnonempty specified hspecified t (draw t)
      (hselected t) hf action (List.mem_toFinset.mp ha) q
  · intro t _
    rw [← hnext t]
    exact physicalNode_clipped_upper source target U N P F A T delta choices node hM hsize hP hF hA hseed hT
      (t + 1) q

end PhysicalNode

end EditApproximation

end OAI
