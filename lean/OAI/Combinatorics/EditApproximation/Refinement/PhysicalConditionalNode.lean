import OAI.Combinatorics.EditApproximation.Refinement.PhysicalParentDraw
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalResampledRegret

namespace OAI

/-!
# Conditional expected regret in a fixed child environment

Finite Bernstein bounds control the parent product draws. Agreement of
deeper selection functions fixes all child histories by locality, and
list membership connects the sampled actions to the refinement recurrence.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

abbrev BandParentSpace (R M b F Q K : ℕ) :=
  ParentRandomSpace R (optimizerTriangularMass K) M (groupDyadicScales M b F).length
    (fun scale => groupSampleCount M Q b (groupDyadicScaleAt M b F scale))

noncomputable def bandParentLaw (R M b F Q K : ℕ) [NeZero M] [NeZero (optimizerTriangularMass K)]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] : Measure (BandParentSpace R M b F Q K) :=
  parentDrawLaw R (optimizerTriangularMass K) M (groupDyadicScales M b F).length
    (fun scale => groupSampleCount M Q b (groupDyadicScaleAt M b F scale))

theorem physical_conditional_node_regret {α : Type*} [DecidableEq α]
    (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 1764 ≤ inputSmallLog N)
    {M J P F b Q thetaExponent R H G K : ℕ}
    [NeZero M] [NeZero R] [NeZero (optimizerTriangularMass K)]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
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
    (reference : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (cell : ℕ × ℕ)
    (hnonempty : physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent
      (rationalParameters F).tau cell ≠ [])
    (specified : UnskippedBand source target (physicalSourceInterval source.length node)
      b P thetaExponent (rationalParameters F).tau F
      (physicalBandChildMassTable source target U N P F A T node hbelow)
      (physicalBandChildInitial source target U N P F A node hbelow))
    (hspecified : specified ∈ physicalNodeCellBands source target U N P F A T node hbelow b thetaExponent
      (rationalParameters F).tau cell)
    (hrep : (b, specified.center) ∈ stageRepresentatives source target U N P F A node)
    (q : TargetInterval target.length)
    (hb : (b : ℝ) ≤ stateEditCost (physicalSource source node) target q)
    (comparison : Fin M → TargetInterval target.length) (hc : comparison ∈ specified.actions)
    (hG : G = H + (bandCoordinates specified.actions.toFinset).card + 2) (hK : K = G ^ 80)
    (htau : 0 < (rationalParameters F).tau)
    (hηrange : (η : ℝ) * (2 * (delta : ℝ) + 8 * ((128 * F : ℚ) : ℝ) *
      (((2 : ℚ) ^ (-(thetaExponent : ℤ))) : ℝ)) ≤ (κ : ℝ))
    (herror : 2 * (rationalParameters F).gamma +
      512 * (128 * F : ℚ) * F * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ κ * delta)
    (realizations : BandParentSpace R M b F Q K → PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (hgroupsFixed : ∀ ω label, node.1.val < label.1.val →
      (realizations ω).groups label = reference.groups label)
    (honlineFixed : ∀ ω label, node.1.val < label.1.val →
      (realizations ω).online label = reference.online label)
    (honlineWire : ∀ ω t, sharedBandRationalAction specified.center
      (physicalBandOnlineDraw source target U N P F A T delta reference node hbelow
        b thetaExponent (rationalParameters F).tau specified.center specified.nonempty η κ G K t
          (parentOnlineDraw ω t)) ∈
      physicalNodeOnline source target U N P F A T delta (realizations ω) node hbelow t q)
    (hgroupWire : ∀ ω t,
      (physicalNodeSelectedGroup source target U N P F A T delta reference node hbelow
        b thetaExponent Q (rationalParameters F).tau cell hnonempty t (parentGroupDraw ω t)).rationalAction ∈
      physicalNodeGroups source target U N P F A T delta (realizations ω) node hbelow t)
    (bernstein : ∀ scale : Fin (groupDyadicScales M b F).length, FiniteBernsteinInput
      (Measure.pi fun _ : Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) =>
        (PMF.uniformOfFintype (Fin M)).toMeasure)) (S : ℕ) :
    let c : ℝ := stateEditCost (physicalSource source node) target q
    let charge : ℝ := ((128 * F : ℚ) : ℝ) * targetEndpointDistance q specified.center
    let clipped := physicalComparisonClipped source target U N P F A T delta reference node hbelow comparison
    (∫ ω, (∑ t ∈ range S,
      (max c (physicalRefinement source target U N P F A T delta (realizations ω) node (t + 1) q : ℝ) -
        charge - clipped (t + 1))) ∂bandParentLaw R M b F Q K) ≤
      ((∑ child, specified.envelope child : ℚ) : ℝ) *
        (Real.log (bandCoordinates specified.actions.toFinset).card / (η : ℝ) + 2 * (κ : ℝ) +
          (S : ℝ) / (H : ℝ) ^ 3) +
        2 * (delta : ℝ) * c + 2 * S * (1 / (H : ℝ) ^ 4) * F * c := by
  let c : ℝ := stateEditCost (physicalSource source node) target q
  let charge : ℝ := ((128 * F : ℚ) : ℝ) * targetEndpointDistance q specified.center
  let history := physicalBandHistory source target U N P F A T delta reference node hbelow
  let clipped := physicalComparisonClipped source target U N P F A T delta reference node hbelow comparison
  let sample := fun t integer => physicalBandOnlineDraw source target U N P F A T delta reference node hbelow
    b thetaExponent (rationalParameters F).tau specified.center specified.nonempty η κ G K t integer
  let failure := fun t draw => physicalNodeGroupFailure source target U N P F A T delta reference node hbelow
    b thetaExponent Q (rationalParameters F).tau cell t draw (rationalParameters F).gamma
  let crossing := firstCrossing specified.actions.toFinset S
    (fun t => bandActionCost charge (fun t coordinate => (history t coordinate : ℝ)) (t + 1)) c
  let prefixPayoff := fun t integer => sampledPrefixRegret charge (κ : ℝ)
    (fun t coordinate => (history t coordinate : ℝ)) clipped (fun j => sample j integer) t
  let regret := fun ω t => max c
    (physicalRefinement source target U N P F A T delta (realizations ω) node (t + 1) q : ℝ) - charge - clipped (t + 1)
  let budget := ((∑ child, specified.envelope child : ℚ) : ℝ) *
    (Real.log (bandCoordinates specified.actions.toFinset).card / (η : ℝ) + 2 * (κ : ℝ) + (S : ℝ) / (H : ℝ) ^ 3)
  have hpoint (ω : BandParentSpace R M b F Q K) : (∑ t ∈ range S, regret ω t) ≤
      (∑ t ∈ range crossing, prefixPayoff t (parentOnlineDraw ω t)) + 2 * (delta : ℝ) * c +
        (2 * (F : ℝ) * c) * ∑ t ∈ range S, (if failure t (parentGroupDraw ω t) then (1 : ℝ) else 0) := by
    have hdet := physicalNode_resampled_regret source target U N P F A T delta
      reference (realizations ω) node hbelow hM hsize hP hF hA hseed hT
      (hgroupsFixed ω) (honlineFixed ω) hleaf b thetaExponent Q (rationalParameters F).tau
      (rationalParameters F).gamma κ htau hdelta hκ hκhalf cell hnonempty specified hspecified hrep q hb comparison hc
      (fun t => sample t (parentOnlineDraw ω t))
      (fun t => physicalBandOnlineDraw_mem source target U N P F A T delta reference node hbelow
        b thetaExponent (rationalParameters F).tau specified.center specified.nonempty η κ G K t (parentOnlineDraw ω t))
      (fun t => parentGroupDraw ω t) (honlineWire ω) (hgroupWire ω) herror S
    have hprefixEq : (∑ t ∈ range crossing, sampledPrefixRegret charge (κ : ℝ)
        (fun t coordinate => (history t coordinate : ℝ)) clipped
        (fun j => sample j (parentOnlineDraw ω j)) t) =
        ∑ t ∈ range crossing, prefixPayoff t (parentOnlineDraw ω t) := by
      apply sum_congr rfl
      intro t _
      exact sampledPrefixRegret_current_sample_congr charge (κ : ℝ)
        (fun t coordinate => (history t coordinate : ℝ)) clipped
        (fun j => sample j (parentOnlineDraw ω j))
        (fun j => sample j (parentOnlineDraw ω t)) t rfl
    change (∑ t ∈ range S, regret ω t) ≤
      (∑ t ∈ range crossing, sampledPrefixRegret charge (κ : ℝ)
        (fun t coordinate => (history t coordinate : ℝ)) clipped
        (fun j => sample j (parentOnlineDraw ω j)) t) + 2 * (delta : ℝ) * c +
        (2 * (F : ℝ) * c) * ∑ t ∈ range S,
          (if failure t (parentGroupDraw ω t) then (1 : ℝ) else 0) at hdet
    rw [hprefixEq] at hdet
    exact hdet
  have hprefix : (∑ t ∈ range crossing, uniformMean (prefixPayoff t)) ≤ budget := by
    exact physicalBand_prefix_expected_regret source target U N P F A T delta reference node hbelow
      b thetaExponent (rationalParameters F).tau specified.center hM hsize hP hF hA hseed hT htau hdelta.le
      specified.nonempty crossing S H G K (firstCrossing_le _ _ _ _) η κ hG hK comparison hc hH hη hκ hκhalf hηrange charge
  have hfailure t (_ht : t < S) :
      (groupSharedDrawLaw (M := M) (fun scale : Fin (groupDyadicScales M b F).length =>
        groupSampleCount M Q b (groupDyadicScaleAt M b F scale))).real {draw | failure t draw = true} ≤
          1 / (H : ℝ) ^ 4 := by
    rw [hHeq]
    exact physicalNode_groupFailure_probability source target N hN hell hM hMeq hPeq hFeq eb hbeq hQeq hthetaeq
      U A hsize hP hA hseed T hT delta reference node hbelow t cell bernstein
  have hbound := parentDrawLaw_firstCrossing_bound R (optimizerTriangularMass K) M
    (groupDyadicScales M b F).length
    (fun scale => groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) S crossing regret prefixPayoff failure
    budget (2 * (delta : ℝ) * c) (2 * (F : ℝ) * c) (1 / (H : ℝ) ^ 4)
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg F))
      (Nat.cast_nonneg _)) hpoint hprefix hfailure
  dsimp only
  change (∫ ω, (∑ t ∈ range S, regret ω t) ∂bandParentLaw R M b F Q K) ≤
    budget + 2 * (delta : ℝ) * c + 2 * S * (1 / (H : ℝ) ^ 4) * F * c
  have hchargeEq : (2 * (F : ℝ) * c) * (S : ℝ) * (1 / (H : ℝ) ^ 4) =
      2 * S * (1 / (H : ℝ) ^ 4) * F * c := by ring
  exact hbound.trans_eq (by rw [hchargeEq])

end EditApproximation

end OAI
