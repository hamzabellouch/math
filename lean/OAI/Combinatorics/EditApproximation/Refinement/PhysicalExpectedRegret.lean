import OAI.Combinatorics.EditApproximation.Refinement.PhysicalNodeRegret
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalGroupAccuracy

namespace OAI

/-! Conditional prefix regret from the exact physical-band sampler. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem uniformMean_sub {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    uniformMean (fun ω => f ω - g ω) = uniformMean f - uniformMean g := by
  simp only [uniformMean, sum_sub_distrib, sub_div]

theorem sampledPrefixRegret_child_identity {β σ : Type*} [Fintype β]
    (charge κ : ℝ) (table : ℕ → β × σ → ℝ)
    (clipped : ℕ → ℝ) (sample : ℕ → β → σ) (t : ℕ) :
    sampledPrefixRegret charge κ table clipped sample t =
      (∑ child, table (t + 1) (child, sample t child)) +
        κ * ((∑ child, table t (child, sample t child)) -
          ∑ child, table (t + 1) (child, sample t child)) - clipped (t + 1) := by
  unfold sampledPrefixRegret bandActionCost
  ring

section PhysicalPrefix

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T : ℕ) (delta : ℚ)
  (choices : PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A))
  (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (b thetaExponent : ℕ) (tau : ℚ) (r : TargetInterval target.length)

local notation "band" => physicalBandActions source target U N P F A T node hbelow b thetaExponent tau r
local notation "mass" => physicalBandEnvelope source target U N P F A T node hbelow b thetaExponent tau r
local notation "history" => physicalBandHistory source target U N P F A T delta choices node hbelow
local notation "theta" => (2 : ℚ) ^ (-(thetaExponent : ℤ))

variable (hM : 0 < M) (hsize : source.length + target.length ≤ N)
  (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (hT : 0 < T)

include hM hsize hP hF hA hseed hT in
/-- Every deterministic prefix uses the same actual computed online mixtures.
Clipping comparison children only decreases the prefix regret. -/
theorem physicalBand_prefix_expected_regret (htau : 0 < tau) (hdelta : 0 ≤ delta)
    (hband : band ≠ []) (C S H G K : ℕ) (hCS : C ≤ S) (η κ : ℚ)
    (hG : G = H + (bandCoordinates (band).toFinset).card + 2) (hK : K = G ^ 80)
    (comparison : Fin M → TargetInterval target.length) (hc : comparison ∈ band)
    (hH : 4 ≤ H) (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hηrange : (η : ℝ) *
      (2 * (delta : ℝ) + 8 * ((128 * F : ℚ) : ℝ) * (theta : ℝ)) ≤ (κ : ℝ)) (charge : ℝ) :
    (∑ t ∈ range C, uniformMean (fun integer : Fin (optimizerTriangularMass K) =>
      sampledPrefixRegret charge (κ : ℝ) (fun t coordinate => (history t coordinate : ℝ))
        (physicalComparisonClipped source target U N P F A T delta choices node hbelow comparison)
        (fun j => physicalBandOnlineDraw source target U N P F A T delta choices node hbelow
          b thetaExponent tau r hband η κ G K j integer) t)) ≤
      ((∑ child, mass child : ℚ) : ℝ) *
        (Real.log (bandCoordinates (band).toFinset).card / (η : ℝ) + 2 * (κ : ℝ) +
          (S : ℝ) / (H : ℝ) ^ 3) := by
  have hGpos : 0 < G := by omega
  have hKpos : 0 < K := by rw [hK]; exact pow_pos hGpos 80
  let : NeZero (optimizerTriangularMass K) := ⟨Nat.ne_of_gt (optimizerTriangularMass_positive K hKpos)⟩
  have hcost := physicalBandOnlineDraw_cost_regret source target U N P F A T delta choices node hbelow
    b thetaExponent tau r hM hsize hP hF hA hseed hT htau hdelta hband C H G K η κ hG hK
    hc hH hη hκ hκhalf hηrange
  have hcomparison : (∑ t ∈ range C, ∑ child, (history (t + 1) (child, comparison child) : ℝ)) ≤
      ∑ t ∈ range C,
        physicalComparisonClipped source target U N P F A T delta choices node hbelow comparison (t + 1) := by
    apply sum_le_sum
    intro t _
    exact sum_le_sum fun i _ => le_max_right _ _
  have hmass : (0 : ℝ) ≤ ((∑ child, mass child : ℚ) : ℝ) :=
    (Rat.cast_nonneg (K := ℝ)).mpr (sum_nonneg fun i _ =>
      (physicalBandEnvelope_pos source target U N P F A T node hbelow b thetaExponent tau r i).le)
  have hprefix : (C : ℝ) / (H : ℝ) ^ 3 ≤ (S : ℝ) / (H : ℝ) ^ 3 :=
    div_le_div_of_nonneg_right (by exact_mod_cast hCS) (pow_nonneg (Nat.cast_nonneg H) 3)
  have hbudget := mul_le_mul_of_nonneg_left hprefix hmass
  simp_rw [sampledPrefixRegret_child_identity, uniformMean_sub, uniformMean_const]
  rw [sum_sub_distrib]
  nlinarith only [hcost, hcomparison, hbudget]

end PhysicalPrefix


theorem unskippedGroupFailure_true {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P thetaExponent : ℕ) (tau F : ℚ)
    (child initial value : Fin M → TargetInterval target.length → ℚ) (Q : ℕ)
    (members : List (UnskippedBand source target parent b P thetaExponent tau F child initial))
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M) (gamma : ℚ) :
    unskippedGroupFailure source target parent b P thetaExponent tau F child initial value Q members draw gamma = true ↔
      ∃ member ∈ members, gamma * b < |dyadicUnskippedGroupEstimate Q value member draw -
        rationalEndpointActionValue member.center member.rounded value| := by
  simp only [unskippedGroupFailure, List.any_eq_true, decide_eq_true_eq]

/-- Per-scale finite Bernstein bounds imply the whole-cell failure probability. -/
theorem physicalNode_groupFailure_probability {α : Type*} [DecidableEq α]
    (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 1764 ≤ inputSmallLog N)
    {M J P F b Q thetaExponent : ℕ} [NeZero M]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (hM : 0 < M) (hMeq : M = (integerParameters N).M)
    (hPeq : P = (integerParameters N).P) (hFeq : F = inputSmallLog N)
    (eb : ℕ) (hbeq : b = 2 ^ eb) (hQeq : Q = inputSmallLog N ^ 80)
    (hthetaeq : thetaExponent = 40 * smallLogExponent N)
    (U : PhysicalEntry M J target.length → ℕ) (A : ℚ)
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A))
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (t : ℕ) (cell : ℕ × ℕ)
    (bernstein : ∀ scale : Fin (groupDyadicScales M b F).length, FiniteBernsteinInput
      (Measure.pi fun _ : Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) =>
        (PMF.uniformOfFintype (Fin M)).toMeasure)) :
    (groupSharedDrawLaw (fun scale : Fin (groupDyadicScales M b F).length =>
      groupSampleCount M Q b (groupDyadicScaleAt M b F scale))).real
      {draw | physicalNodeGroupFailure source target U N P F A T delta choices node hbelow
        b thetaExponent Q (rationalParameters F).tau cell t draw (rationalParameters F).gamma = true} ≤
      1 / (inputHeight N : ℝ) ^ 4 := by
  subst F
  let F := inputSmallLog N
  let scales := groupDyadicScaleAt M b (F : ℚ)
  let count := fun scale : Fin (groupDyadicScales M b F).length => groupSampleCount M Q b (scales scale)
  have hscales : List.ofFn scales = groupDyadicScales M b F := List.ofFn_get _
  have hprob := physical_cellGroupEstimate_failure source target N hN hell hM hMeq hPeq eb hbeq hQeq hthetaeq
    U A hsize hP hA hseed T hT delta choices node hbelow (t + 1) cell scales count hscales (fun _ => rfl) bernstein
  dsimp only at hprob
  let members := physicalNodeCellBands source target U N P F A T node hbelow
    b thetaExponent (rationalParameters F).tau cell
  let value := fun i s => physicalBandHistory source target U N P F A T delta choices node hbelow (t + 1) (i, s)
  have hevent : {draw | physicalNodeGroupFailure source target U N P F A T delta choices node hbelow
      b thetaExponent Q (rationalParameters F).tau cell t draw (rationalParameters F).gamma = true} =
      {draw | ∃ member ∈ members, ((rationalParameters F).gamma : ℝ) * b <
        |((dyadicUnskippedGroupEstimate Q value member draw -
          rationalEndpointActionValue member.center member.rounded value : ℚ) : ℝ)|} := by
    ext draw
    simp only [Set.mem_ofPred_eq, physicalNodeGroupFailure, unskippedGroupFailure_true]
    change (∃ member ∈ members, (rationalParameters F).gamma * b <
        |dyadicUnskippedGroupEstimate Q value member draw -
          rationalEndpointActionValue member.center member.rounded value|) ↔ _
    constructor
    · rintro ⟨member, hm, he⟩
      refine ⟨member, hm, ?_⟩
      exact_mod_cast he
    · rintro ⟨member, hm, he⟩
      refine ⟨member, hm, ?_⟩
      exact_mod_cast he
  rw [hevent]
  exact hprob

end EditApproximation

end OAI
