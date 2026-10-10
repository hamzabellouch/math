import OAI.Combinatorics.EditApproximation.Refinement.PhysicalTreeRegret

namespace OAI

/-! Finite expectation of the actual clipped refinement telescope. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

section Expectation

variable {α Ω : Type*} [DecidableEq α] [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {M J : ℕ} (source target : List α) (hM : 0 < M)
  (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
  (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T : ℕ) (hT : 0 < T) (delta : ℚ)
  (choices : Ω → PhysicalSelections M J source.length target.length P
    (stageRepresentatives source target U N P F A)) (rootQ : TargetInterval target.length)
  (μ : Measure Ω) [IsProbabilityMeasure μ]

local notation "D" => (stateEditCost source target rootQ : ℝ)
local notation "root" => (Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit : PhysicalNode M J)
local notation "lifted" => fun ω => physicalClippedLift source target hM U N P F A hP T delta (choices ω) rootQ
local notation "frontier" => comparisonFrontier source target hM P hP
  (some (sourceIntervalAt M source.length 0 PUnit.unit, rootQ))

include hsize hF hA hseed hT in
 theorem physical_tree_expected_excess (S : ℕ) (hS : 0 < S)
    (hcapacity : source.length ≤ M ^ J) (hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2)
    (budget : (d : ℕ) → TreeLayer M d → ℝ)
    (hnode : ∀ d < J, ∀ path : TreeLayer M d,
      (∫ ω, (∑ t ∈ range S,
        (lifted ω (t + 1) d path - (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path) -
          ∑ i : Fin M, lifted ω (t + 1) (d + 1) (path, i))) ∂μ) ≤ budget d path) :
    (∫ ω, max ((physicalRefinement source target U N P F A T delta (choices ω) root S rootQ : ℝ) - D) 0 ∂μ) ≤
      ((8 * (M : ℝ) + 512 * F) * J / P) * D +
        (∑ d ∈ range J, ∑ path : TreeLayer M d, budget d path) / S := by
  let charge := fun d (path : TreeLayer M d) => (128 * (F : ℝ)) * comparisonMovement source target P (frontier d path)
  let regret := fun ω t d (path : TreeLayer M d) =>
    lifted ω (t + 1) d path - charge d path - ∑ i : Fin M, lifted ω (t + 1) (d + 1) (path, i)
  let coefficient : ℝ := (8 * (M : ℝ) + 512 * F) * J / P
  have hpoint (ω : Ω) := physical_tree_regret_time source target hM U N P F A hsize hP hF hA hseed
    T hT delta (choices ω) rootQ S hcapacity hsmall
  have hmean := integral_mono (μ := μ) (.of_finite) (.of_finite) hpoint
  have hregret : (∫ ω, (∑ t ∈ range S, ∑ d ∈ range J, ∑ path : TreeLayer M d, regret ω t d path) ∂μ) ≤
      ∑ d ∈ range J, ∑ path : TreeLayer M d, budget d path := by
    have hswap (ω : Ω) : (∑ t ∈ range S, ∑ d ∈ range J, ∑ path : TreeLayer M d, regret ω t d path) =
        ∑ d ∈ range J, ∑ path : TreeLayer M d, ∑ t ∈ range S, regret ω t d path := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      rw [sum_comm]
    simp_rw [hswap]
    rw [integral_finsetSum _ (by intro d hd; exact .of_finite)]
    apply sum_le_sum
    intro d hd
    rw [integral_finsetSum _ (by intro path hp; exact .of_finite)]
    exact sum_le_sum fun path _ => hnode d (mem_range.mp hd) path
  have hroot : (∫ ω, max D
      (physicalRefinement source target U N P F A T delta (choices ω) root S rootQ : ℝ) ∂μ) =
      (∫ ω, max ((physicalRefinement source target U N P F A T delta (choices ω) root S rootQ : ℝ) - D) 0 ∂μ) + D := by
    have heq (ω : Ω) : max D
        (physicalRefinement source target U N P F A T delta (choices ω) root S rootQ : ℝ) =
        max ((physicalRefinement source target U N P F A T delta (choices ω) root S rootQ : ℝ) - D) 0 + D := by
      rw [← max_add_add_right, sub_add_cancel, zero_add, max_comm]
    simp_rw [heq]
    rw [integral_add (.of_finite) (integrable_const _), integral_const, probReal_univ, one_smul]
  change (∫ ω, (S : ℝ) * max D
      (physicalRefinement source target U N P F A T delta (choices ω) root S rootQ : ℝ) ∂μ) ≤
    (∫ ω, (S : ℝ) * ((1 + coefficient) * D) +
      (∑ t ∈ range S, ∑ d ∈ range J, ∑ path : TreeLayer M d, regret ω t d path) ∂μ) at hmean
  rw [integral_const_mul, integral_add (integrable_const _) (.of_finite),
    integral_const, probReal_univ, one_smul, hroot] at hmean
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  apply (sub_le_iff_le_add').mp
  apply (le_div_iff₀ hSR).2
  nlinarith only [hmean, hregret]

end Expectation

end EditApproximation

end OAI
