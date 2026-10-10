import OAI.Combinatorics.EditApproximation.Refinement.PhysicalNodeRegret
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRefinementLocality

namespace OAI

/-! The deterministic first-crossing transfer under literal parent-only resampling. -/

namespace EditApproximation

open Finset

/-- A sampled regret at time t uses only the action sampled at that time. -/
theorem sampledPrefixRegret_current_sample_congr {β σ : Type*} [Fintype β]
    (charge κ : ℝ) (table : ℕ → β × σ → ℝ) (clipped : ℕ → ℝ)
    (first second : ℕ → β → σ) (t : ℕ) (heq : first t = second t) :
    sampledPrefixRegret charge κ table clipped first t =
      sampledPrefixRegret charge κ table clipped second t := by
  simp only [sampledPrefixRegret, heq]

theorem physicalNode_resampled_regret {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
    (reference choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hM : 0 < M) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (hT : 0 < T)
    (hgroupsFixed : ∀ label, node.1.val < label.1.val → choices.groups label = reference.groups label)
    (honlineFixed : ∀ label, node.1.val < label.1.val → choices.online label = reference.online label)
    (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (b thetaExponent Q : ℕ) (tau gamma κ : ℚ) (htau : 0 < tau)
    (hdelta : 0 < delta) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (cell : ℕ × ℕ)
    (hnonempty : physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell ≠ [])
    (specified : UnskippedBand source target (physicalSourceInterval source.length node)
      b P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node hbelow)
      (physicalBandChildInitial source target U N P F A node hbelow))
    (hspecified : specified ∈ physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent tau cell)
    (hrep : (b, specified.center) ∈ stageRepresentatives source target U N P F A node)
    (q : TargetInterval target.length) (hb : (b : ℝ) ≤ stateEditCost (physicalSource source node) target q)
    (comparison : Fin M → TargetInterval target.length) (hc : comparison ∈ specified.actions)
    (sample : ℕ → Fin M → TargetInterval target.length) (hsample : ∀ t, sample t ∈ specified.actions)
    (draw : ℕ → ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (honline : ∀ t, sharedBandRationalAction specified.center (sample t) ∈
      physicalNodeOnline source target U N P F A T delta choices node hbelow t q)
    (hselected : ∀ t, (physicalNodeSelectedGroup source target U N P F A T delta reference node hbelow
      b thetaExponent Q tau cell hnonempty t (draw t)).rationalAction ∈
      physicalNodeGroups source target U N P F A T delta choices node hbelow t)
    (herror : 2 * gamma + 512 * (128 * F : ℚ) * F * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ κ * delta)
    (S : ℕ) :
    let c : ℝ := stateEditCost (physicalSource source node) target q
    let charge : ℝ := ((128 * F : ℚ) : ℝ) * targetEndpointDistance q specified.center
    let history := physicalBandHistory source target U N P F A T delta reference node hbelow
    let clipped := physicalComparisonClipped source target U N P F A T delta reference node hbelow comparison
    let failure := fun t => physicalNodeGroupFailure source target U N P F A T delta reference node hbelow
      b thetaExponent Q tau cell t (draw t) gamma
    let crossing := firstCrossing specified.actions.toFinset S
      (fun t => bandActionCost charge (fun t coordinate => (history t coordinate : ℝ)) (t + 1)) c
    (∑ t ∈ range S, (max c
      (physicalRefinement source target U N P F A T delta choices node (t + 1) q : ℝ) - charge - clipped (t + 1))) ≤
      (∑ t ∈ range crossing, sampledPrefixRegret charge (κ : ℝ)
        (fun t coordinate => (history t coordinate : ℝ)) clipped sample t) + 2 * (delta : ℝ) * c +
          2 * (F : ℝ) * c * ∑ t ∈ range S, (if failure t then (1 : ℝ) else 0) := by
  have hchildren := physicalRefinement_children_fixed source target U N P F A T delta
    choices reference node hbelow hgroupsFixed honlineFixed
  have hhistory : physicalBandHistory source target U N P F A T delta choices node hbelow =
      physicalBandHistory source target U N P F A T delta reference node hbelow := by
    funext t coordinate
    exact congrFun (congrFun (congrFun hchildren coordinate.1) t) coordinate.2
  have hselected' t :
      (physicalNodeSelectedGroup source target U N P F A T delta choices node hbelow
        b thetaExponent Q tau cell hnonempty t (draw t)).rationalAction ∈
      physicalNodeGroups source target U N P F A T delta choices node hbelow t := by
    simpa only [physicalNodeSelectedGroup, hhistory] using hselected t
  have hdet := physicalNode_firstCrossing_regret source target U N P F A T delta choices node hbelow
    hM hsize hP hF hA hseed hT hleaf b thetaExponent Q tau gamma κ htau hdelta hκ hκhalf
    cell hnonempty specified hspecified hrep q hb comparison hc sample hsample draw honline hselected' herror S
  have hclipped : physicalComparisonClipped source target U N P F A T delta choices node hbelow comparison =
      physicalComparisonClipped source target U N P F A T delta reference node hbelow comparison := by
    funext t
    simp only [physicalComparisonClipped, hhistory]
  have hfailure : physicalNodeGroupFailure source target U N P F A T delta choices node hbelow
      b thetaExponent Q tau cell = physicalNodeGroupFailure source target U N P F A T delta reference node hbelow
      b thetaExponent Q tau cell := by
    funext t draw gamma
    simp only [physicalNodeGroupFailure, hhistory]
  dsimp only at hdet ⊢
  rw [hhistory, hclipped, hfailure] at hdet
  exact hdet

end EditApproximation

end OAI
