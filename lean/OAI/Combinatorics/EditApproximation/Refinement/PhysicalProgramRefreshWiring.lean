import OAI.Combinatorics.EditApproximation.Refinement.PhysicalProgramLaw
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalConditionalNode

namespace OAI

/-! Exact candidate wiring and complete-child locality under actual two-key refresh. -/

namespace EditApproximation

section RefreshWiring

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T thetaExponent H Q : ℕ) (tau delta η κ : ℚ)
  (node : PhysicalInternalNode M J)
  (representative : Fin (stageRepresentatives source target U N P F A node.1).length)
  (scale : Fin (dyadicScales N).length)
  (cell : Fin (physicalProgramCells source target U N P F A thetaExponent node.1
    ((dyadicScales N).get scale)).length)

local notation "onlineKey" => (Sigma.mk node representative : PhysicalOnlineKey source target U N P F A)
local notation "groupKey" => (Sigma.mk node (Sigma.mk scale cell) : PhysicalGroupKey source target U N P F A thetaExponent)
local notation "b" => List.get (dyadicScales N) scale
local notation "groupCell" => List.get (physicalProgramCells source target U N P F A thetaExponent (Subtype.val node) b) cell
local notation "G" => physicalProgramBandG source target U N P F A T thetaExponent H tau node representative
local notation "K" => physicalProgramBandK source target U N P F A T thetaExponent H tau node representative
local notation "Draw" => PhysicalProgramDraw (R := R) source target U N P F A T thetaExponent H Q tau
local notation "Fresh" => PhysicalOnlineArray (R := R) source target U N P F A T thetaExponent H tau onlineKey ×
  PhysicalGroupArray (R := R) source target U N P F A thetaExponent Q groupKey
local notation "choices" => physicalProgramDrawSelections source target U N P F A T thetaExponent H Q tau η κ
local notation "refresh" => physicalProgramRefresh source target U N P F A T thetaExponent H Q tau

/-- Complete child histories remain fixed under replacement of the two
actual random arrays at this parent. -/
theorem physicalProgramRefresh_history (draw : Draw) (fresh : Fresh) :
    physicalBandHistory source target U N P F A T delta (choices (refresh draw onlineKey groupKey fresh)) node.1 node.2 =
      physicalBandHistory source target U N P F A T delta (choices draw) node.1 node.2 := by
  have hchildren := physicalRefinement_children_fixed source target U N P F A T delta
    (choices (refresh draw onlineKey groupKey fresh)) (choices draw) node.1 node.2
    (fun label hdeeper => (physicalProgramDrawSelections_refresh_deeper source target U N P F A T thetaExponent H Q tau η κ
      draw onlineKey groupKey fresh label hdeeper hdeeper).1)
    (fun label hdeeper => (physicalProgramDrawSelections_refresh_deeper source target U N P F A T thetaExponent H Q tau η κ
      draw onlineKey groupKey fresh label hdeeper hdeeper).2)
  funext t coordinate
  exact congrFun (congrFun (congrFun hchildren coordinate.1) t) coordinate.2

theorem physicalProgramRefresh_clipped (draw : Draw) (fresh : Fresh)
    (comparison : Fin M → TargetInterval target.length) :
    physicalComparisonClipped source target U N P F A T delta
      (choices (refresh draw onlineKey groupKey fresh)) node.1 node.2 comparison =
        physicalComparisonClipped source target U N P F A T delta (choices draw) node.1 node.2 comparison := by
  funext t
  simp only [physicalComparisonClipped,
    physicalProgramRefresh_history source target U N P F A T thetaExponent H Q tau delta η κ
      node representative scale cell draw fresh]

/-- The literal online slot supplies the reference-environment sampler
at the refreshed integer; no candidate-list premise remains. -/
theorem physicalProgramRefresh_online_mem (draw : Draw) (fresh : Fresh)
    (member : UnskippedBand source target (physicalSourceInterval source.length node.1)
      b P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node.1 node.2)
      (physicalBandChildInitial source target U N P F A node.1 node.2))
    (hget : (stageRepresentatives source target U N P F A node.1).get representative = (b, member.center))
    (t : ℕ) (q : TargetInterval target.length)
    (hquery : physicalProgramOnlineGuard source target U N P F A node.1 q (b, member.center)) :
    sharedBandRationalAction member.center
      (physicalBandOnlineDraw source target U N P F A T delta (choices draw) node.1 node.2
        b thetaExponent tau member.center member.nonempty η κ G K t (parentOnlineDraw fresh t)) ∈
      physicalNodeOnline source target U N P F A T delta
        (choices (refresh draw onlineKey groupKey fresh)) node.1 node.2 t q := by
  let streams := physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau
    (refresh draw onlineKey groupKey fresh)
  have hmem := physicalProgram_online_action_mem source target U N P F A T thetaExponent H Q tau η κ
    streams.1 streams.2 delta node representative b member hget t q hquery
  have hhistory := physicalProgramRefresh_history source target U N P F A T thetaExponent H Q tau delta η κ
    node representative scale cell draw fresh
  have hinteger := congrFun (physicalProgramRefresh_online source target U N P F A T thetaExponent H Q tau
    draw onlineKey groupKey fresh) (Fin.ofNat R t)
  change streams.1 node representative (Fin.ofNat R t) = parentOnlineDraw fresh t at hinteger
  change sharedBandRationalAction member.center
    (physicalBandOnlineDraw source target U N P F A T delta
      (choices (refresh draw onlineKey groupKey fresh)) node.1 node.2 b thetaExponent tau member.center
      member.nonempty η κ G K t (streams.1 node representative (Fin.ofNat R t))) ∈
      physicalNodeOnline source target U N P F A T delta
        (choices (refresh draw onlineKey groupKey fresh)) node.1 node.2 t q at hmem
  simpa only [physicalBandOnlineDraw, hhistory, hinteger] using hmem

/-- The literal whole-cell slot supplies the selected group computed from
the unchanged complete child environment and refreshed shared arrays. -/
theorem physicalProgramRefresh_group_mem (draw : Draw) (fresh : Fresh)
    (hnonempty : physicalNodeCellBands source target U N P F A T node.1 node.2 b thetaExponent tau groupCell ≠ [])
    (t : ℕ) :
    (physicalNodeSelectedGroup source target U N P F A T delta (choices draw) node.1 node.2
      b thetaExponent Q tau groupCell hnonempty t (parentGroupDraw fresh t)).rationalAction ∈
      physicalNodeGroups source target U N P F A T delta
        (choices (refresh draw onlineKey groupKey fresh)) node.1 node.2 t := by
  let streams := physicalProgramDrawStreams source target U N P F A T thetaExponent H Q tau
    (refresh draw onlineKey groupKey fresh)
  have hmem := physicalProgram_group_action_mem source target U N P F A T thetaExponent H Q tau η κ
    streams.1 streams.2 delta node scale cell hnonempty t
  have hhistory := physicalProgramRefresh_history source target U N P F A T thetaExponent H Q tau delta η κ
    node representative scale cell draw fresh
  have hdraw := congrFun (physicalProgramRefresh_group source target U N P F A T thetaExponent H Q tau
    draw onlineKey groupKey fresh) (Fin.ofNat R t)
  change streams.2 node scale cell (Fin.ofNat R t) = parentGroupDraw fresh t at hdraw
  change (physicalNodeSelectedGroup source target U N P F A T delta
    (choices (refresh draw onlineKey groupKey fresh)) node.1 node.2 b thetaExponent Q tau groupCell hnonempty t
    (streams.2 node scale cell (Fin.ofNat R t))).rationalAction ∈
      physicalNodeGroups source target U N P F A T delta
        (choices (refresh draw onlineKey groupKey fresh)) node.1 node.2 t at hmem
  simpa only [physicalNodeSelectedGroup, hhistory, hdraw] using hmem

end RefreshWiring

end EditApproximation

end OAI
