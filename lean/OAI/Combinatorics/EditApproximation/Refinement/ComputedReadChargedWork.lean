import OAI.Combinatorics.EditApproximation.Refinement.ComputedIndexedCoarseWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseSamplingWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedExecutionCosts
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarsePreparation
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open Filter MeasureTheory

/-- Execution budget including indexed coarse computation, consumed threshold
bits, rejection sampling, dictionary operations, address construction and unit charges. -/


theorem computedExecutionReadChargedWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionReadChargedWork source target N) (computedExecutionLaw source target N) :=
  (((computedExecutionIndexedCoarseWork_integrable source target N).add
    (computedExecutionCoarseSamplingWork_integrable source target N)).add
    (computedExecutionNonlocalWork_integrable source target N)).add
    (computedExecutionCoarsePreparationWork_integrable source target N)

theorem computedExecutionReadChargedWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3) →
      (∫ execution, computedExecutionReadChargedWork source target N execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hh : 0 < epsilon / 2 := half_pos hepsilon
  filter_upwards [computedExecutionIndexedCoarseWork_expected_near_linear (epsilon / 2) hh,
    computedExecutionCoarseSamplingWork_expected_near_linear (epsilon / 2) hh,
    computedExecutionNonlocalWork_expected_near_linear (epsilon / 2) hh,
    computedExecutionCoarsePreparationWork_expected_near_linear (epsilon / 2) hh,
    constant_le_rpow_eventually 4 (epsilon / 2) hh] with N hc hs hn hp hfour
  intro source target hsize hsymbol
  have hiC := computedExecutionIndexedCoarseWork_integrable source target N
  have hiS := computedExecutionCoarseSamplingWork_integrable source target N
  have hiN := computedExecutionNonlocalWork_integrable source target N
  have hiP := computedExecutionCoarsePreparationWork_integrable source target N
  change integral (computedExecutionLaw source target N)
    (((computedExecutionIndexedCoarseWork source target N + computedExecutionCoarseSamplingWork source target N) +
      computedExecutionNonlocalWork source target N) + computedExecutionCoarsePreparationWork source target N) ≤ _
  rw [integral_add' ((hiC.add hiS).add hiN) hiP, integral_add' (hiC.add hiS) hiN, integral_add' hiC hiS]
  calc
    _ ≤ 4 * (N + 2 : ℝ) ^ (1 + epsilon / 2) := by
      linarith only [hc source target hsize hsymbol, hs source target hsize, hn source target hsize, hp source target hsize hsymbol]
    _ ≤ (N + 2 : ℝ) ^ (epsilon / 2) * (N + 2 : ℝ) ^ (1 + epsilon / 2) :=
      mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end EditApproximation

end OAI
