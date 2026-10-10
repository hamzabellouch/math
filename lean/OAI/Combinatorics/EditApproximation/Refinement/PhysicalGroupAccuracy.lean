import OAI.Combinatorics.EditApproximation.Refinement.ComputedGroupAccuracy
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRefinementSpatial

namespace OAI

/-! Group concentration specialized to the actual stage and complete child histories. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem physical_cellGroupEstimate_failure {α : Type*} [DecidableEq α]
    (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 1764 ≤ inputSmallLog N)
    {M J P b Q thetaExponent K : ℕ} [NeZero M]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (hM : 0 < M) (hMeq : M = (integerParameters N).M)
    (hPeq : P = (integerParameters N).P) (eb : ℕ) (hbeq : b = 2 ^ eb)
    (hQeq : Q = inputSmallLog N ^ 80) (hthetaeq : thetaExponent = 40 * smallLogExponent N)
    (U : PhysicalEntry M J target.length → ℕ) (A : ℚ)
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P (inputSmallLog N) A))
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (t : ℕ) (cell : ℕ × ℕ)
    (scales : Fin K → ℚ) (count : Fin K → ℕ)
    (hscales : List.ofFn scales = groupDyadicScales M b (inputSmallLog N))
    (hcount : ∀ scale, count scale = groupSampleCount M Q b (scales scale))
    (bernstein : ∀ scale : Fin K, FiniteBernsteinInput
      (Measure.pi fun _ : Fin (count scale) => (PMF.uniformOfFintype (Fin M)).toMeasure)) :
    let F := inputSmallLog N
    let initial := fun i s => stageInitial source target U N P F A (physicalChild node hbelow i, s)
    let child := fun i s => stageWarmupMass source target U N P F A T (physicalChild node hbelow i, s)
    let value := fun i s => physicalRefinement source target U N P F A T delta choices
      (physicalChild node hbelow i) t s
    let members := cellUnskippedBands source target (physicalSourceInterval source.length node)
      b P F thetaExponent (rationalParameters F).tau (refinementFactor A F)
      (fun s => stageInitial source target U N P F A (node, s)) child initial cell
    (groupSharedDrawLaw count).real
      {draw | ∃ member ∈ members, ((rationalParameters F).gamma : ℝ) * b <
        |((unskippedGroupEstimate scales count value member draw -
          rationalEndpointActionValue member.center member.rounded value : ℚ) : ℝ)|} ≤
      1 / (inputHeight N : ℝ) ^ 4 := by
  have hF : 1 ≤ inputSmallLog N := Nat.one_le_two_pow
  apply computed_cellGroupEstimate_failure source target N hN hell hM hMeq hPeq eb hbeq hQeq hthetaeq
    (physicalSourceInterval source.length node) (refinementFactor A (inputSmallLog N))
    (fun s => stageInitial source target U N P (inputSmallLog N) A (node, s))
    (fun i s => stageWarmupMass source target U N P (inputSmallLog N) A T (physicalChild node hbelow i, s))
    (fun i s => stageInitial source target U N P (inputSmallLog N) A (physicalChild node hbelow i, s))
    (fun i s => physicalRefinement source target U N P (inputSmallLog N) A T delta choices
      (physicalChild node hbelow i) t s) cell scales count hscales hcount
  · intro i s r
    have hf := refinementFactor_spec A (inputSmallLog N) (by omega)
    exact physicalInitialTable_spatial source target U N P (inputSmallLog N) A
      (refinementFactor A (inputSmallLog N)) hsize hP hF hA hf.1 hf.2 hseed
      (physicalChild node hbelow i) s r
  · intro i s
    have h := physicalRefinement_stage_bounds source target hM U N P (inputSmallLog N) A
      hsize hP hF hA hseed T hT delta choices (physicalChild node hbelow i) t s
    exact ⟨physicalRefinement_nonneg source target hM U N P (inputSmallLog N) A
      hsize hP hF hA hseed T hT delta choices (physicalChild node hbelow i) t s,
      h.2.1.trans (h.2.2.1.trans h.2.2.2.1)⟩
  · exact bernstein

end EditApproximation

end OAI
