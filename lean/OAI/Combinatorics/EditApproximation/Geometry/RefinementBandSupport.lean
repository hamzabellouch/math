import OAI.Combinatorics.EditApproximation.Geometry.RefinementInitialSupport
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Band-table congruence uses proof-free data. Equality of these data
preserves the ordered minimization and its tie decisions, even though the
guard records have different table-indexed types. -/

namespace EditApproximation

abbrev UnskippedBandData (M ny : ℕ) :=
  TargetInterval ny × (Fin M → ℚ) × (Fin M → TargetInterval ny)

def UnskippedBand.data {α : Type*} {source target : List α} {M b P exponent : ℕ}
    {parent : TargetInterval source.length} {tau F : ℚ}
    {child initial : Fin M → TargetInterval target.length → ℚ}
    (member : UnskippedBand source target parent b P exponent tau F child initial) :
    UnskippedBandData M target.length :=
  (member.center, member.envelope, member.rounded)

def UnskippedBandData.action {M ny : ℕ} (data : UnskippedBandData M ny) :
    PhysicalRationalAction M ny :=
  ⟨data.1, endpointActionConnection data.1 data.2.2, fun i => (i, data.2.2 i)⟩

def UnskippedBandData.estimate {M ny : ℕ} (b Q : ℕ) (F : ℚ)
    (value : Fin M → TargetInterval ny → ℚ)
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (data : UnskippedBandData M ny) : ℚ :=
  groupMemberEstimate (groupDyadicScaleAt M b F)
    (fun scale => groupSampleCount M Q b (groupDyadicScaleAt M b F scale))
    (endpointActionConnection data.1 data.2.2) data.2.1 (fun i => value i (data.2.2 i)) draw

theorem rational_argmax_map {ι κ : Type*} (members : List ι) (project : ι → κ)
    (score : κ → ℚ) :
    (members.argmax (fun member => score (project member))).map project =
      (members.map project).argmax score := by
  induction members with
  | nil => rfl
  | cons first rest ih =>
    rw [List.map_cons, List.argmax_cons, List.argmax_cons, ← ih]
    cases hmax : rest.argmax (fun member => score (project member)) with
    | none => rfl
    | some selected =>
      dsimp only [Option.map]
      split_ifs <;> rfl

theorem testUnskippedBand_center_of_some {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (tau F : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ) (r : TargetInterval target.length)
    (member : UnskippedBand source target parent b P exponent tau F child initial)
    (hmember : testUnskippedBand source target parent b P exponent tau F child initial r = some member) :
    member.center = r := by
  have h := testUnskippedBand_center_projection source target parent r b P exponent tau F child initial
  rw [hmember] at h
  simpa only [Option.map_some, Option.isSome_some, Bool.true_eq, ite_true, Option.some.injEq] using h

theorem unskippedBand_data_congr {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P exponent : ℕ) (tau F : ℚ)
    (child child' initial initial' : Fin M → TargetInterval target.length → ℚ)
    (hchild : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, child i (action i) = child' i (action i))
    (hinitial : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, initial i (action i) = initial' i (action i))
    (left : UnskippedBand source target parent b P exponent tau F child initial)
    (right : UnskippedBand source target parent b P exponent tau F child' initial')
    (hleft : left.center = r) (hright : right.center = r) : left.data = right.data := by
  have hband := representativeBandActions_congr_child source target parent r b P tau
    ((2 : ℚ) ^ (-(exponent : ℤ))) child child' hchild
  have hinitialBand : ∀ action ∈ representativeBandActions source target parent r b P tau
      ((2 : ℚ) ^ (-(exponent : ℤ))) child, ∀ i, initial i (action i) = initial' i (action i) := by
    intro action ha i
    exact hinitial action (representativeBandActions_wide source target parent r b P tau _ child action ha) i
  apply Prod.ext (hleft.trans hright.symm)
  apply Prod.ext
  · change left.envelope = right.envelope
    unfold UnskippedBand.envelope UnskippedBand.actions
    rw [hleft, hright]
    exact representativeBandEnvelope_congr source target parent r b P exponent tau
      child child' initial initial' hchild hinitial
  · change left.rounded = right.rounded
    have hactions : left.actions = right.actions := by
      simp only [UnskippedBand.actions, hleft, hright]
      exact hband
    have hrightInitial : ∀ action ∈ right.actions,
        ∀ i, initial i (action i) = initial' i (action i) := by
      intro action ha i
      simp only [UnskippedBand.actions, hright, ← hband] at ha
      exact hinitialBand action ha i
    exact (UnskippedBand.canonicalRounded_congr exponent b left.actions right.actions
      hactions left.nonempty right.nonempty initial).trans
      (canonicalRoundedBandAction_congr_initial exponent b right.actions right.nonempty
        initial initial' hrightInitial)

theorem testUnskippedBand_data_congr {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P exponent : ℕ) (tau F : ℚ)
    (child child' initial initial' : Fin M → TargetInterval target.length → ℚ)
    (hchild : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, child i (action i) = child' i (action i))
    (hinitial : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, initial i (action i) = initial' i (action i)) :
    (testUnskippedBand source target parent b P exponent tau F child initial r).map UnskippedBand.data =
      (testUnskippedBand source target parent b P exponent tau F child' initial' r).map UnskippedBand.data := by
  have haccept := testUnskippedBand_isSome_congr source target parent r b P exponent tau F
    child child' initial initial' hchild hinitial
  cases hleft : testUnskippedBand source target parent b P exponent tau F child initial r with
  | none =>
    cases hright : testUnskippedBand source target parent b P exponent tau F child' initial' r with
    | none => rfl
    | some right => simp only [hleft, hright, Option.isSome_none, Option.isSome_some, Bool.false_eq_true] at haccept
  | some left =>
    cases hright : testUnskippedBand source target parent b P exponent tau F child' initial' r with
    | none => simp only [hleft, hright, Option.isSome_none, Option.isSome_some, Bool.true_eq_false] at haccept
    | some right =>
      apply congrArg some
      exact unskippedBand_data_congr source target parent r b P exponent tau F child child' initial initial'
        hchild hinitial left right
        (testUnskippedBand_center_of_some source target parent b P exponent tau F child initial r left hleft)
        (testUnskippedBand_center_of_some source target parent b P exponent tau F child' initial' r right hright)

theorem unskippedBandList_data_congr {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (tau F : ℚ)
    (child child' initial initial' : Fin M → TargetInterval target.length → ℚ)
    (centers : List (TargetInterval target.length))
    (hchild : ∀ r ∈ centers, ∀ action ∈ wideActionList M parent r b P,
      ∀ i, child i (action i) = child' i (action i))
    (hinitial : ∀ r ∈ centers, ∀ action ∈ wideActionList M parent r b P,
      ∀ i, initial i (action i) = initial' i (action i)) :
    (unskippedBandList source target parent b P exponent tau F child initial centers).map UnskippedBand.data =
      (unskippedBandList source target parent b P exponent tau F child' initial' centers).map UnskippedBand.data := by
  simp only [unskippedBandList, List.map_filterMap]
  apply List.filterMap_congr
  intro r hr
  exact testUnskippedBand_data_congr source target parent r b P exponent tau F
    child child' initial initial' (hchild r hr) (hinitial r hr)

theorem chooseCellGroupAction_data {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M) :
    chooseCellGroupAction source target parent b P F exponent Q tau a parentInitial
      child initial current cell draw =
      (((cellUnskippedBands source target parent b P F exponent tau a parentInitial child initial cell).map
        UnskippedBand.data).argmax (fun data => -data.estimate b Q F current draw)).map UnskippedBandData.action := by
  let members := cellUnskippedBands source target parent b P F exponent tau a parentInitial child initial cell
  change (if h : members = [] then none else some (chooseUnskippedGroup Q current members h draw).rationalAction) = _
  rw [← rational_argmax_map members UnskippedBand.data (fun data => -data.estimate b Q F current draw)]
  by_cases hnil : members = []
  · simp only [hnil, dite_true, List.argmax_nil, Option.map_none]
  · rw [dite_eq_right hnil]
    unfold chooseUnskippedGroup selectGroupMember
    change some (UnskippedBand.rationalAction
        ((members.argmax (fun member => -member.data.estimate b Q F current draw)).getD (members.head hnil))) = _
    cases hmax : members.argmax (fun member => -member.data.estimate b Q F current draw) with
    | none => exact False.elim (hnil (List.argmax_eq_none.mp hmax))
    | some selected => rfl

theorem chooseCellGroupAction_congr_bandTables {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child child' initial initial' current : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (hchild : ∀ r ∈ cellRepresentativeStates target.length P F b a parentInitial
        ((2 : ℚ) ^ (-(exponent : ℤ))) cell, ∀ action ∈ wideActionList M parent r b P,
      ∀ i, child i (action i) = child' i (action i))
    (hinitial : ∀ r ∈ cellRepresentativeStates target.length P F b a parentInitial
        ((2 : ℚ) ^ (-(exponent : ℤ))) cell, ∀ action ∈ wideActionList M parent r b P,
      ∀ i, initial i (action i) = initial' i (action i)) :
    chooseCellGroupAction source target parent b P F exponent Q tau a parentInitial
      child initial current cell draw =
    chooseCellGroupAction source target parent b P F exponent Q tau a parentInitial
      child' initial' current cell draw := by
  rw [chooseCellGroupAction_data, chooseCellGroupAction_data]
  rw [show (cellUnskippedBands source target parent b P F exponent tau a parentInitial child initial cell).map
      UnskippedBand.data =
      (cellUnskippedBands source target parent b P F exponent tau a parentInitial child' initial' cell).map
        UnskippedBand.data from
    unskippedBandList_data_congr source target parent b P exponent tau F child child' initial initial' _
      hchild hinitial]

/-- Keep the optimizer opaque while transporting the finite band data. -/
def bandDataOnlineCandidate {M ny : ℕ} (band : List (Fin M → TargetInterval ny))
    (envelope : Fin M → ℚ) (H : ℕ) (eta kappa : ℚ)
    (children : PhysicalChildTables M ny) (t : ℕ) (r : TargetInterval ny)
    (integer : ℕ) (accepted : Bool) : Option (PhysicalRationalAction M ny) :=
  let G := H + (bandCoordinates band.toFinset).card + 2
  let K := G ^ 80
  let sample := boundedOnlineInteger (optimizerTriangularMass K)
    (optimizerTriangularMass_positive _ (pow_pos (by omega : 0 < G) 80)) integer
  if hband : band = [] then none else
    if accepted then some (sharedBandRationalAction r (finiteOptimizerActionDraw band hband envelope
      (rationalOnlineLinear eta kappa
        (childGain envelope (fun s coordinate => children coordinate.1 s coordinate.2))
        (childDecrement envelope (fun s coordinate => children coordinate.1 s coordinate.2)) t)
      G K sample))
    else none

theorem keyedOnlineCandidate_test_form {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (tau eta kappa : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (r : TargetInterval target.length) (integer : ℕ) :
    keyedOnlineCandidate source target parent P F exponent H b tau eta kappa
      child initial children t r integer =
    bandDataOnlineCandidate
      (representativeBandActions source target parent r b P tau ((2 : ℚ) ^ (-(exponent : ℤ))) child)
      (bandChildEnvelope b
        (representativeBandActions source target parent r b P tau ((2 : ℚ) ^ (-(exponent : ℤ))) child) initial)
      H eta kappa children t r integer
      (testUnskippedBand source target parent b P exponent tau F child initial r).isSome := by
  unfold keyedOnlineCandidate bandDataOnlineCandidate
  dsimp only
  by_cases hband : representativeBandActions source target parent r b P tau
      ((2 : ℚ) ^ (-(exponent : ℤ))) child = []
  · simp only [dite_eq_left hband]
  · simp only [dite_eq_right hband]
    cases testUnskippedBand source target parent b P exponent tau F child initial r <;> rfl

theorem keyedOnlineCandidate_congr_bandTables {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (tau eta kappa : ℚ)
    (child child' initial initial' : Fin M → TargetInterval target.length → ℚ)
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (r : TargetInterval target.length) (integer : ℕ)
    (hchild : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, child i (action i) = child' i (action i))
    (hinitial : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, initial i (action i) = initial' i (action i)) :
    keyedOnlineCandidate source target parent P F exponent H b tau eta kappa
      child initial children t r integer =
    keyedOnlineCandidate source target parent P F exponent H b tau eta kappa
      child' initial' children t r integer := by
  have hband := representativeBandActions_congr_child source target parent r b P tau
    ((2 : ℚ) ^ (-(exponent : ℤ))) child child' hchild
  have henv := representativeBandEnvelope_congr source target parent r b P exponent tau
    child child' initial initial' hchild hinitial
  have htest := testUnskippedBand_isSome_congr source target parent r b P exponent tau F
    child child' initial initial' hchild hinitial
  rw [keyedOnlineCandidate_test_form, keyedOnlineCandidate_test_form]
  rw [htest, henv, hband]

theorem wideWarmupInputs_pair {nx ny M : ℕ} (parent : TargetInterval nx) (P b : ℕ)
    (representatives : List (ℕ × TargetInterval ny)) (r : TargetInterval ny)
    (hrep : (b, r) ∈ representatives) (action : Fin M → TargetInterval ny)
    (haction : action ∈ wideActionList M parent r b P) (i : Fin M) :
    (i, action i) ∈ wideWarmupInputs parent P representatives := by
  apply List.mem_eraseDups.mpr
  apply List.mem_flatMap.mpr
  refine ⟨(b, r), hrep, List.mem_flatMap.mpr ?_⟩
  exact ⟨i, List.mem_finRange i, List.mem_map.mpr
    ⟨action i, finiteAssignments_sound M _ action haction i, rfl⟩⟩



section QueryBands

variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child child' initial initial' current : Fin M → TargetInterval target.length → ℚ)
  (children : PhysicalChildTables M target.length)
  (integer : ℕ → TargetInterval target.length → ℕ) (draw : CellGroupDraws M F Q)
  (q : TargetInterval target.length)
  (hchild : ∀ input ∈ refinementBandInputList parent N P F exponent a parentInitial q,
    child input.1 input.2 = child' input.1 input.2)
  (hinitial : ∀ input ∈ refinementBandInputList parent N P F exponent a parentInitial q,
    initial input.1 input.2 = initial' input.1 input.2)

include hchild hinitial

theorem localOnlineCandidates_congr_bandTables :
    localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial children t integer q =
    localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child' initial' children t integer q := by
  unfold localOnlineCandidates
  apply List.filterMap_congr
  intro b hb
  dsimp only
  split_ifs with heligible
  · apply keyedOnlineCandidate_congr_bandTables source target parent P F exponent H b tau eta kappa
      child child' initial initial' children t _ _
    · intro action ha i
      exact hchild _ (wideWarmupInputs_pair parent P b _ _
        (queryEarlierRepresentatives_online N P F exponent a parentInitial q b hb) action ha i)
    · intro action ha i
      exact hinitial _ (wideWarmupInputs_pair parent P b _ _
        (queryEarlierRepresentatives_online N P F exponent a parentInitial q b hb) action ha i)
  · rfl

theorem localCellGroupActions_congr_bandTables :
    localCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw q =
    localCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child' initial' current draw q := by
  unfold localCellGroupActions
  apply List.flatMap_congr
  intro b hb
  apply List.filterMap_congr
  intro cell hc
  have hkey : (b, cell) ∈ localGroupQueryKeys N F exponent a parentInitial q :=
    List.mem_flatMap.mpr ⟨b, hb, List.mem_map.mpr ⟨cell, hc, rfl⟩⟩
  apply chooseCellGroupAction_congr_bandTables source target parent b P F exponent Q tau a
    parentInitial child child' initial initial' current cell (draw b cell)
  · intro r hr action ha i
    exact hchild _ (wideWarmupInputs_pair parent P b _ r
      (queryEarlierRepresentatives_cell N P F exponent a parentInitial q (b, cell) hkey r hr) action ha i)
  · intro r hr action ha i
    exact hinitial _ (wideWarmupInputs_pair parent P b _ r
      (queryEarlierRepresentatives_cell N P F exponent a parentInitial q (b, cell) hkey r hr) action ha i)

end QueryBands

end EditApproximation

end OAI
