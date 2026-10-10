import OAI.Combinatorics.EditApproximation.Refinement.PhysicalNodeRegret
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Finite online and whole-cell candidate programs

Physical selections use the representative and guarded band lists. Each
band has its own finite optimizer stream; every whole cell has shared
per-scale child streams. These streams define coherent finite tables.
-/

namespace EditApproximation

open Finset



section Program

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T thetaExponent H Q : ℕ) (tau η κ : ℚ)

local notation "representatives" => stageRepresentatives source target U N P F A
local notation "theta" => (2 : ℚ) ^ (-(thetaExponent : ℤ))

def physicalProgramBandG (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) : ℕ :=
  let br := (representatives node.1).get representative
  H + (bandCoordinates (physicalBandActions source target U N P F A T node.1 node.2
    br.1 thetaExponent tau br.2).toFinset).card + 2

def physicalProgramBandK (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) : ℕ :=
  (physicalProgramBandG source target U N P F A T thetaExponent H tau node representative) ^ 80

theorem physicalProgramBandG_spec (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) (b : ℕ)
    (member : UnskippedBand source target (physicalSourceInterval source.length node.1)
      b P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node.1 node.2)
      (physicalBandChildInitial source target U N P F A node.1 node.2))
    (hget : (representatives node.1).get representative = (b, member.center)) :
    physicalProgramBandG source target U N P F A T thetaExponent H tau node representative =
      H + (bandCoordinates member.actions.toFinset).card + 2 := by
  simp only [physicalProgramBandG, hget, physicalBandActions, UnskippedBand.actions]


theorem physicalProgramBandG_ge_two (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) :
    2 ≤ physicalProgramBandG source target U N P F A T thetaExponent H tau node representative := by
  dsimp only [physicalProgramBandG]
  omega

theorem physicalProgramBandK_positive (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) :
    0 < physicalProgramBandK source target U N P F A T thetaExponent H tau node representative := by
  exact pow_pos (lt_of_lt_of_le (by norm_num : 0 < 2)
    (physicalProgramBandG_ge_two source target U N P F A T thetaExponent H tau node representative)) 80


def physicalProgramCells (node : PhysicalNode M J) (b : ℕ) : List (ℕ × ℕ) :=
  (((representatives node).filter fun br => decide (br.1 = b)).map
    fun br => targetCell (theta * b) br.2).eraseDups

def physicalBandOnlineCandidate (node : PhysicalInternalNode M J)
    (br : ℕ × TargetInterval target.length) (children : PhysicalChildTables M target.length)
    (t G K : ℕ) (integer : Fin (optimizerTriangularMass K)) :
    Option (PhysicalRationalAction M target.length) :=
  let band := physicalBandActions source target U N P F A T node.1 node.2 br.1 thetaExponent tau br.2
  if hband : band = [] then none else
    match testUnskippedBand source target (physicalSourceInterval source.length node.1)
      br.1 P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node.1 node.2)
      (physicalBandChildInitial source target U N P F A node.1 node.2) br.2 with
    | none => none
    | some _ => some (sharedBandRationalAction br.2
      (finiteOptimizerActionDraw band hband
        (physicalBandEnvelope source target U N P F A T node.1 node.2 br.1 thetaExponent tau br.2)
        (rationalOnlineLinear η κ
          (childGain (physicalBandEnvelope source target U N P F A T node.1 node.2 br.1 thetaExponent tau br.2)
            (fun t coordinate => children coordinate.1 t coordinate.2))
          (childDecrement (physicalBandEnvelope source target U N P F A T node.1 node.2 br.1 thetaExponent tau br.2)
            (fun t coordinate => children coordinate.1 t coordinate.2)) t)
        G
        K integer))

def physicalProgramOnlineCandidate (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) (children : PhysicalChildTables M target.length)
    (t : ℕ)
    (integer : Fin (optimizerTriangularMass
      (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative))) :
    Option (PhysicalRationalAction M target.length) :=
  physicalBandOnlineCandidate source target U N P F A T thetaExponent tau η κ node
    ((representatives node.1).get representative) children t
    (physicalProgramBandG source target U N P F A T thetaExponent H tau node representative)
    (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative) integer

abbrev PhysicalOnlineStreams (R : ℕ) := ∀ node : PhysicalInternalNode M J,
  ∀ representative : Fin (representatives node.1).length,
    Fin R → Fin (optimizerTriangularMass
      (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative))

abbrev PhysicalGroupStreams (R : ℕ) := ∀ node : PhysicalInternalNode M J,
  ∀ scale : Fin (dyadicScales N).length,
    ∀ _cell : Fin (physicalProgramCells source target U N P F A thetaExponent node.1
      ((dyadicScales N).get scale)).length,
      Fin R → ∀ h : Fin (groupDyadicScales M ((dyadicScales N).get scale) F).length,
        Fin (groupSampleCount M Q ((dyadicScales N).get scale)
          (groupDyadicScaleAt M ((dyadicScales N).get scale) F h)) → Fin M

/-- The literal online query uses its one rounded center at each allowed
scale, with the scale window tested against the literal initial table. -/
def physicalProgramOnlineGuard (node : PhysicalNode M J) (q : TargetInterval target.length)
    (br : ℕ × TargetInterval target.length) : Prop :=
  br.2 = roundInterval (seedGridSpacing br.1 P) q ∧
    stageInitial source target U N P F A (node, q) / (16 * F) ≤ br.1 ∧
    (br.1 : ℚ) ≤ 8 * refinementFactor A F * stageInitial source target U N P F A (node, q)

instance physicalProgramOnlineGuard_decidable (node : PhysicalNode M J) (q : TargetInterval target.length)
    (br : ℕ × TargetInterval target.length) :
    Decidable (physicalProgramOnlineGuard source target U N P F A node q br) := by
  unfold physicalProgramOnlineGuard
  infer_instance

/-- The actual dyadic comparison center passes the query filter on every
good initial seed; no local scale premise is assumed. -/
theorem physicalProgramOnlineGuard_comparison
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalNode M J) (q : TargetInterval target.length)
    (hc : 0 < stateEditCost (physicalSource source node) target q) :
    let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
    physicalProgramOnlineGuard source target U N P F A node q
      (b, roundInterval (seedGridSpacing b P) q) := by
  let b := 2 ^ Nat.log 2 (stateEditCost (physicalSource source node) target q)
  let a := refinementFactor A F
  let w := stageInitial source target U N P F A (node, q)
  have hfactor := refinementFactor_spec A F (by omega : 0 < F)
  have ha : (0 : ℚ) < a := lt_of_lt_of_le zero_lt_one hfactor.1
  have hFpos : (0 : ℚ) < F := Nat.cast_pos.2 (by omega : 0 < F)
  have hbounds := physicalInitialTable_bounds source target U N P F A (refinementFactor A F)
    hsize hP hF hA hfactor.1 hfactor.2 hseed (node, q)
  have hlower : (stateEditCost (physicalSource source node) target q : ℚ) / a ≤ w :=
    (le_max_left _ _).trans hbounds.1
  have hupper : w ≤ 2 * F * stateEditCost (physicalSource source node) target q := hbounds.2
  have hdyadic := cost_dyadicScale _ _ hc le_rfl
  have hblo : (b : ℚ) ≤ stateEditCost (physicalSource source node) target q := by exact_mod_cast hdyadic.2.1
  have hchi : (stateEditCost (physicalSource source node) target q : ℚ) ≤ 2 * b := by exact_mod_cast hdyadic.2.2.le
  have hw : 0 ≤ w := (div_nonneg (Nat.cast_nonneg _) ha.le).trans hlower
  change _ ∧ w / (16 * F) ≤ b ∧ (b : ℚ) ≤ 8 * a * w
  refine ⟨rfl, ?_, ?_⟩
  · apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℚ) < 16) hFpos)).2
    have hmul := mul_le_mul_of_nonneg_left hchi (show (0 : ℚ) ≤ 2 * F by positivity)
    have hwb : w ≤ 4 * F * b := by nlinarith only [hupper, hmul]
    have hFb : (0 : ℚ) ≤ F * b := mul_nonneg hFpos.le (Nat.cast_nonneg b)
    nlinarith only [hwb, hFb]
  · have hca : (stateEditCost (physicalSource source node) target q : ℚ) ≤ a * w := by
      simpa only [mul_comm] using (div_le_iff₀ ha).mp hlower
    have haw : (0 : ℚ) ≤ a * w := mul_nonneg ha.le hw
    nlinarith only [hblo, hca, haw]

def physicalProgramOnline {R : ℕ} [NeZero R]
    (stream : PhysicalOnlineStreams source target U N P F A T thetaExponent H tau R)
    (node : PhysicalNode M J) (children : PhysicalChildTables M target.length) (t : ℕ)
    (q : TargetInterval target.length) : List (PhysicalRationalAction M target.length) :=
  if hbelow : node.1.val < J then
    ((List.finRange (representatives node).length).filter fun representative => decide
      (physicalProgramOnlineGuard source target U N P F A node q ((representatives node).get representative))).filterMap fun representative =>
      physicalProgramOnlineCandidate source target U N P F A T thetaExponent H tau η κ
        ⟨node, hbelow⟩ representative children (t - 1)
          (stream ⟨node, hbelow⟩ representative (Fin.ofNat R (t - 1)))
  else []

def physicalProgramGroups {R : ℕ} [NeZero R]
    (stream : PhysicalGroupStreams source target U N P F A thetaExponent Q R)
    (node : PhysicalNode M J) (children : PhysicalChildTables M target.length) (t : ℕ) :
    List (PhysicalRationalAction M target.length) :=
  if hbelow : node.1.val < J then
    (List.finRange (dyadicScales N).length).flatMap fun scale =>
      (List.finRange (physicalProgramCells source target U N P F A thetaExponent node
        ((dyadicScales N).get scale)).length).filterMap fun cell =>
        chooseCellGroupAction source target (physicalSourceInterval source.length node)
          ((dyadicScales N).get scale) P F thetaExponent Q tau (refinementFactor A F)
          (fun q => stageInitial source target U N P F A (node, q))
          (physicalBandChildMassTable source target U N P F A T node hbelow)
          (physicalBandChildInitial source target U N P F A node hbelow)
          (fun i q => children i t q)
          ((physicalProgramCells source target U N P F A thetaExponent node
            ((dyadicScales N).get scale)).get cell)
          (stream ⟨node, hbelow⟩ scale cell (Fin.ofNat R (t - 1)))
  else []

/-- Every produced online candidate is literally one of the parent wide actions. -/
theorem physicalProgramOnlineCandidate_wide (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) (children : PhysicalChildTables M target.length)
    (t : ℕ)
    (integer : Fin (optimizerTriangularMass
      (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative)))
    (action : PhysicalRationalAction M target.length)
    (hselected : physicalProgramOnlineCandidate source target U N P F A T thetaExponent H tau η κ
      node representative children t integer = some action) :
    action ∈ rationalActualWideActions (physicalSourceInterval source.length node.1)
      (representatives node.1) P := by
  let br := (representatives node.1).get representative
  have hrep : br ∈ representatives node.1 := List.get_mem _ _
  unfold physicalProgramOnlineCandidate physicalBandOnlineCandidate at hselected
  dsimp only at hselected
  split_ifs at hselected with hband
  split at hselected
  · cases hselected
  · cases hselected
    exact sharedBandRationalAction_wide source target (physicalSourceInterval source.length node.1) br.2
      (representatives node.1) br.1 P tau theta
      (physicalBandChildMassTable source target U N P F A T node.1 node.2) hrep _
      (finiteOptimizerActionDraw_mem _ hband _ _ _ _ _)

theorem physicalProgramOnline_wide {R : ℕ} [NeZero R]
    (stream : PhysicalOnlineStreams source target U N P F A T thetaExponent H tau R)
    (node : PhysicalNode M J) (children : PhysicalChildTables M target.length) (t : ℕ)
    (q : TargetInterval target.length) (action : PhysicalRationalAction M target.length)
    (hselected : action ∈ physicalProgramOnline source target U N P F A T thetaExponent H tau η κ
      stream node children t q) :
    action ∈ rationalActualWideActions (physicalSourceInterval source.length node)
      (representatives node) P := by
  unfold physicalProgramOnline at hselected
  split_ifs at hselected with hbelow
  · obtain ⟨representative, _, hselected⟩ := List.mem_filterMap.mp hselected
    exact physicalProgramOnlineCandidate_wide source target U N P F A T thetaExponent H tau η κ
      ⟨node, hbelow⟩ representative children _ _ action hselected
  · exact False.elim (List.not_mem_nil hselected)

theorem physicalProgramGroups_wide {R : ℕ} [NeZero R]
    (stream : PhysicalGroupStreams source target U N P F A thetaExponent Q R)
    (node : PhysicalNode M J) (children : PhysicalChildTables M target.length) (t : ℕ)
    (action : PhysicalRationalAction M target.length)
    (hselected : action ∈ physicalProgramGroups source target U N P F A T thetaExponent Q tau
      stream node children t) :
    action ∈ rationalActualWideActions (physicalSourceInterval source.length node)
      (representatives node) P := by
  unfold physicalProgramGroups at hselected
  split_ifs at hselected with hbelow
  · obtain ⟨scale, _, hscale⟩ := List.mem_flatMap.mp hselected
    obtain ⟨cell, _, hselected⟩ := List.mem_filterMap.mp hscale
    exact chooseCellGroupAction_wide_mem source target (physicalSourceInterval source.length node)
      N ((dyadicScales N).get scale) P F thetaExponent Q tau (refinementFactor A F)
      (fun q => stageInitial source target U N P F A (node, q))
      (physicalBandChildMassTable source target U N P F A T node hbelow)
      (physicalBandChildInitial source target U N P F A node hbelow)
      (fun i q => children i t q) _ _ (List.get_mem _ _) action hselected
  · exact False.elim (List.not_mem_nil hselected)

/-- The actual complete selection interface contains exactly the finite
online and shared whole-cell candidates produced by the streams. -/
def physicalProgramSelections {R : ℕ} [NeZero R]
    (online : PhysicalOnlineStreams source target U N P F A T thetaExponent H tau R)
    (groups : PhysicalGroupStreams source target U N P F A thetaExponent Q R) :
    PhysicalSelections M J source.length target.length P representatives where
  groups := physicalProgramGroups source target U N P F A T thetaExponent Q tau groups
  online := physicalProgramOnline source target U N P F A T thetaExponent H tau η κ online
  groups_mem := physicalProgramGroups_wide source target U N P F A T thetaExponent Q tau groups
  online_mem := physicalProgramOnline_wide source target U N P F A T thetaExponent H tau η κ online

/-- An accepted literal band is retained in its online representative slot. -/
theorem physicalProgramOnlineCandidate_accepted (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) (b : ℕ)
    (member : UnskippedBand source target (physicalSourceInterval source.length node.1)
      b P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node.1 node.2)
      (physicalBandChildInitial source target U N P F A node.1 node.2))
    (hget : (representatives node.1).get representative = (b, member.center))
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (integer : Fin (optimizerTriangularMass
      (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative))) :
    physicalProgramOnlineCandidate source target U N P F A T thetaExponent H tau η κ
      node representative children t integer = some (sharedBandRationalAction member.center
      (finiteOptimizerActionDraw member.actions member.nonempty member.envelope
        (rationalOnlineLinear η κ (childGain member.envelope
          (fun t coordinate => children coordinate.1 t coordinate.2))
          (childDecrement member.envelope (fun t coordinate => children coordinate.1 t coordinate.2)) t)
        (physicalProgramBandG source target U N P F A T thetaExponent H tau node representative)
        (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative) integer)) := by
  unfold physicalProgramOnlineCandidate
  rw [hget]
  simp only [physicalBandOnlineCandidate, physicalBandActions,
    testUnskippedBand_accept member, dite_eq_right member.nonempty]
  rfl

/-- Every eligible center contributes its whole cell to the actual cell loop. -/
theorem physicalProgramCells_complete (node : PhysicalNode M J) (b : ℕ)
    (r : TargetInterval target.length) (hrep : (b, r) ∈ representatives node) :
    targetCell (theta * b) r ∈ physicalProgramCells source target U N P F A thetaExponent node b := by
  apply List.mem_eraseDups.mpr
  apply List.mem_map.mpr
  refine ⟨(b, r), List.mem_filter.mpr ⟨hrep, by simp⟩, rfl⟩


/-- The candidate list contains the sampled shared action at every accepted
representative slot, with the supplied child history and current integer. -/
theorem physicalProgramOnline_contains_accepted {R : ℕ} [NeZero R]
    (stream : PhysicalOnlineStreams source target U N P F A T thetaExponent H tau R)
    (node : PhysicalInternalNode M J)
    (representative : Fin (representatives node.1).length) (b : ℕ)
    (member : UnskippedBand source target (physicalSourceInterval source.length node.1)
      b P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node.1 node.2)
      (physicalBandChildInitial source target U N P F A node.1 node.2))
    (hget : (representatives node.1).get representative = (b, member.center))
    (children : PhysicalChildTables M target.length) (t : ℕ) (q : TargetInterval target.length)
    (hquery : physicalProgramOnlineGuard source target U N P F A node.1 q (b, member.center)) :
    sharedBandRationalAction member.center
      (finiteOptimizerActionDraw member.actions member.nonempty member.envelope
        (rationalOnlineLinear η κ (childGain member.envelope
          (fun t coordinate => children coordinate.1 t coordinate.2))
          (childDecrement member.envelope (fun t coordinate => children coordinate.1 t coordinate.2)) t)
        (physicalProgramBandG source target U N P F A T thetaExponent H tau node representative)
        (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative)
        (stream node representative (Fin.ofNat R t))) ∈
      physicalProgramOnline source target U N P F A T thetaExponent H tau η κ
        stream node.1 children (t + 1) q := by
  rw [physicalProgramOnline, dite_eq_left node.2]
  apply List.mem_filterMap.mpr
  refine ⟨representative, List.mem_filter.mpr ⟨by simp, ?_⟩, ?_⟩
  · simpa only [hget, decide_eq_true_eq] using hquery
  · simpa only [Nat.add_sub_cancel] using
      physicalProgramOnlineCandidate_accepted source target U N P F A T thetaExponent H tau η κ
        node representative b member hget children t (stream node representative (Fin.ofNat R t))

/-- Whole-cell sampling uses the same per-scale arrays for all its members;
the literal selected member is included in the parent candidate list. -/
theorem physicalProgramGroups_contains_selected {R : ℕ} [NeZero R]
    (stream : PhysicalGroupStreams source target U N P F A thetaExponent Q R)
    (node : PhysicalInternalNode M J) (scale : Fin (dyadicScales N).length)
    (cell : Fin (physicalProgramCells source target U N P F A thetaExponent node.1
      ((dyadicScales N).get scale)).length)
    (hnonempty : physicalNodeCellBands source target U N P F A T node.1 node.2
      ((dyadicScales N).get scale) thetaExponent tau
      ((physicalProgramCells source target U N P F A thetaExponent node.1
        ((dyadicScales N).get scale)).get cell) ≠ [])
    (children : PhysicalChildTables M target.length) (t : ℕ) :
    (chooseUnskippedGroup Q (fun i q => children i (t + 1) q)
      (physicalNodeCellBands source target U N P F A T node.1 node.2
        ((dyadicScales N).get scale) thetaExponent tau
        ((physicalProgramCells source target U N P F A thetaExponent node.1
          ((dyadicScales N).get scale)).get cell)) hnonempty
      (stream node scale cell (Fin.ofNat R t))).rationalAction ∈
      physicalProgramGroups source target U N P F A T thetaExponent Q tau stream node.1 children (t + 1) := by
  rw [physicalProgramGroups, dite_eq_left node.2]
  apply List.mem_flatMap.mpr
  refine ⟨scale, by simp, List.mem_filterMap.mpr ⟨cell, by simp, ?_⟩⟩
  unfold physicalNodeCellBands at hnonempty
  simp only [chooseCellGroupAction, Nat.add_sub_cancel, dite_eq_right hnonempty]
  rfl


end Program

end EditApproximation

end OAI
