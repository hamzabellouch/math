import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericKernelPopulations

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem eventually_actual_numericKernel_populations (c η : ℝ)
    (hc : 0 < c) (hη : 0 < η) (hηu : η ≤ 1/10) :
    ∀ᶠ T : ℝ in atTop, let X : ℝ := parameterX T; ∀ (S : Finset ℤ) (m : ℕ) (h : ℤ),
      0 < m → (m : ℝ) ≤ X^(η/10) → IsCoprime h (m : ℤ) →
      (∀ x ∈ S, (m : ℤ)*x-h ≠ 0) →
      (∀ x ∈ S, ∀ y ∈ S, |(x : ℝ)-(y : ℝ)| ≤ X) →
      c*Real.sqrt X/(Real.log X)^3 ≤ S.card →
      ((canonicalKernelImage S m h).card : ℝ) ≤ X^(η/10) →
      ∃ u ∈ canonicalKernelImage S m h,
        0 < |(u : ℝ)| ∧ |(u : ℝ)| ≤ X^η ∧ Squarefree u ∧
        (canonicalKernelRoots S m h u).Nonempty ∧
        X^(1/2-3*η) ≤ (canonicalKernelRoots S m h u).card ∧
        ∀ r ∈ canonicalKernelRoots S m h u, ∀ s ∈ canonicalKernelRoots S m h u,
          |(r : ℝ)-(s : ℝ)| ≤ X^(1/2+η) := by
  exact (tendsto_natCast_atTop_atTop.comp parameterX_tendsto).eventually
    (eventually_numericKernel_populations c η hc hη hηu)

end Ostmann.QuadraticCenter

end

end OAI
