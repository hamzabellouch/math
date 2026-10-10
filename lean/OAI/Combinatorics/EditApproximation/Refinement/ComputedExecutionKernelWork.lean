import OAI.Combinatorics.EditApproximation.Refinement.ComputedKernelWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedReadChargedWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open MeasureTheory Filter



theorem computedExecutionKernelWork_integrable (source target : List ℕ) (N : ℕ)
    (cost : ComputedFamilyInput source target N → ComputedFamilyMemoKey source target N → ℕ) :
    Integrable (computedExecutionKernelWork source target N cost)
      (computedExecutionLaw source target N) :=
  computedExecutionAcceptedWork_integrable source target N
    (fun input => (computedFamilyKernelWork source target N input (cost input) : ℝ))

theorem computedExecutionKernelWork_expected_near_linear (D : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ cost : ComputedFamilyInput source target N → ComputedFamilyMemoKey source target N → ℕ,
      (∀ input key, cost input key ≤ computedLocalKernelBudget D N) →
      (∫ execution, computedExecutionKernelWork source target N cost execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedFamilyKernelWork_near_linear D epsilon hepsilon] with N hN
  intro source target hsize cost hcost
  calc
    _ ≤ ∫ _ : ComputedExecutionOutcome source target N, (N + 2 : ℝ) ^ (1 + epsilon)
        ∂computedExecutionLaw source target N :=
      integral_mono (computedExecutionKernelWork_integrable source target N cost)
        (integrable_const _) (fun execution => hN source target hsize
          (computedExecutionAccepted source target N execution) _ (hcost _))
    _ = _ := by simp

/-- Execution work combines the nonlocal charges with a local kernel annotation. -/


theorem computedExecutionTotalWork_integrable (source target : List ℕ) (N : ℕ)
    (cost : ComputedFamilyInput source target N → ComputedFamilyMemoKey source target N → ℕ) :
    Integrable (computedExecutionTotalWork source target N cost)
      (computedExecutionLaw source target N) :=
  (computedExecutionReadChargedWork_integrable source target N).add
    (computedExecutionKernelWork_integrable source target N cost)

theorem computedExecutionTotalWork_expected_near_linear (D : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ cost : ComputedFamilyInput source target N → ComputedFamilyMemoKey source target N → ℕ,
      (∀ input key, cost input key ≤ computedLocalKernelBudget D N) →
      (∫ execution, computedExecutionTotalWork source target N cost execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hh := half_pos hepsilon
  filter_upwards [computedExecutionReadChargedWork_expected_near_linear (epsilon / 2) hh,
    computedExecutionKernelWork_expected_near_linear D (epsilon / 2) hh,
    constant_le_rpow_eventually 2 (epsilon / 2) hh] with N hn hk htwo
  intro source target hsize hsymbol cost hcost
  change integral (computedExecutionLaw source target N)
    (computedExecutionReadChargedWork source target N + computedExecutionKernelWork source target N cost) ≤ _
  rw [integral_add' (computedExecutionReadChargedWork_integrable source target N)
    (computedExecutionKernelWork_integrable source target N cost)]
  calc
    _ ≤ 2 * (N + 2 : ℝ) ^ (1 + epsilon / 2) := by
      linarith only [hn source target hsize hsymbol, hk source target hsize cost hcost]
    _ ≤ (N + 2 : ℝ) ^ (epsilon / 2) * (N + 2 : ℝ) ^ (1 + epsilon / 2) :=
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end EditApproximation

end OAI
