import OAI.Probability.SignedSweeps.ReverseEncounters

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem conditional_reverse_encounter_bound {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (A : Finset I) (x : InjectiveTuple I (2 ^ d))
    (b : SubsetNetwork A → PhysicalSettings d)
    (hΔ : 0 < 2 * (d : ℝ) * Fintype.card I / (2 ^ d : ℕ))
    (hΔ1 : 2 * (d : ℝ) * Fintype.card I / (2 ^ d : ℕ) ≤ 1) :
    finiteProb (fun p : SubsetNetwork A → PhysicalSettings d =>
      NoIsolatedVertex (endpointEncounter d
        ((mixedNetworkPermutation d A b).symm (mixedNetworkPermutation d A p x))
        (mixedNetworkPermutation d A p x)) Finset.univ) ≤
    (Real.sqrt (2 * (d : ℝ) * Fintype.card I / (2 ^ d : ℕ))) ^ Fintype.card I *
      Real.exp (Real.exp 2 * Fintype.card I) := by
  exact (finiteProb_mono (fun p hp => reverse_endpoint_noIsolates_implies_network A x p b hp)).trans
    (independentSampleSubset_noIsolates_bound (reverseNetworkState d b)
      (networkInitialSubsets A x) (Fintype.card I) (networkInitialSubsets_total A x).symm hΔ hΔ1)

theorem maskedEndpointKernel_square_row_bound {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (A : Finset I) (x : InjectiveTuple I (2 ^ d))
    (hΔ : 0 < 2 * (d : ℝ) * Fintype.card I / (2 ^ d : ℕ))
    (hΔ1 : 2 * (d : ℝ) * Fintype.card I / (2 ^ d : ℕ) ≤ 1) :
    (∑ z, ∑ y, maskedEndpointKernel d A x y * maskedEndpointKernel d A z y) ≤
      (Real.sqrt (2 * (d : ℝ) * Fintype.card I / (2 ^ d : ℕ))) ^ Fintype.card I *
        Real.exp (Real.exp 2 * Fintype.card I) := by
  let e : InjectiveTuple I (2 ^ d) ↪ (I → Fin (2 ^ d)) :=
    ⟨fun x => x, fun x y h => Function.Embedding.ext (congrFun h)⟩
  let K := maskedPermutationKernel (mixedNetworkPermutation d A)
    (fun x y => NoIsolatedVertex (endpointEncounter d x y) Finset.univ)
  have he (x y : InjectiveTuple I (2 ^ d)) : maskedEndpointKernel d A x y = K (e x) (e y) :=
    maskedEndpointKernel_eq_mixed d A x y
  simp only [he]
  refine (nonnegative_kernel_restricted_row_le e K (maskedPermutationKernel_nonneg _ _) x).trans ?_
  refine (maskedPermutationKernel_square_row_le (mixedNetworkPermutation d A)
    (fun x y => NoIsolatedVertex (endpointEncounter d x y) Finset.univ) (e x)).trans ?_
  calc
    _ ≤ finiteMean ℝ (fun _b : SubsetNetwork A → PhysicalSettings d =>
        (Real.sqrt (2 * (d : ℝ) * Fintype.card I / (2 ^ d : ℕ))) ^ Fintype.card I *
          Real.exp (Real.exp 2 * Fintype.card I)) :=
      finiteMean_mono (fun b => conditional_reverse_encounter_bound A x b hΔ hΔ1)
    _ = _ := finiteMean_const ℝ _

theorem sparse_sweep_operator_bound {d : ℕ} (lam : Partition (2 ^ d))
    (hΔ : 0 < 2 * (d : ℝ) * (2 ^ d - lam.1.rowLen 0 : ℕ) / (2 ^ d : ℕ))
    (hΔ1 : 2 * (d : ℝ) * (2 ^ d - lam.1.rowLen 0 : ℕ) / (2 ^ d : ℕ) ≤ 1) :
    ‖(sweepOperator lam).toContinuousLinearMap‖ ≤
      2 ^ (2 ^ d - lam.1.rowLen 0 : ℕ) *
        Real.sqrt ((Real.sqrt (2 * (d : ℝ) * (2 ^ d - lam.1.rowLen 0 : ℕ) / (2 ^ d : ℕ))) ^
          (2 ^ d - lam.1.rowLen 0 : ℕ) * Real.exp (Real.exp 2 * (2 ^ d - lam.1.rowLen 0 : ℕ))) := by
  apply sweep_norm_le_of_masked_rows lam (by positivity)
  intro A x
  have h := maskedEndpointKernel_square_row_bound A x
  simp only [card_offFirstRow] at h
  exact h hΔ hΔ1

end SignedSweeps
end

end OAI
