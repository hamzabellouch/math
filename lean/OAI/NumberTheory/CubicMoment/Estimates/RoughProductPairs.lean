import OAI.NumberTheory.CubicMoment.Estimates.PrimeDetectorStopping
import OAI.NumberTheory.CubicMoment.Estimates.PrimeFactorPairs

namespace OAI

/-! Exact collection of the original rough-product divisor expansion
as independent primary factors, with the original product support. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem roughProduct_primary_factor_pair {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {X : ℝ} (hnX : norm n ≤ X)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (roughProduct ψ w n:ℂ)*K n =
      ∑ q ∈ ((primaryElementBall X).product (primaryElementBall X)).filter
          (fun q => q.1*q.2 = n), cutoffMoebius ψ w q.1*K (q.1*q.2) := by
  rw [←squarefree_primary_factor_pairs hn hs hnX
    (fun d e => cutoffMoebius ψ w d*K (d*e))]
  rw [roughProduct_primary_divisor_sum hn hs,Finset.sum_mul,
    primary_divisors_of_squarefree_eq hn hs,
    Finset.sum_image (primaryPrimeFactors_prod_injective
      (fun p hp => (primaryPrimeFactor_spec hn hp).1))]
  apply Finset.sum_congr rfl
  intro s hsubset
  have hprod := (primaryFactorRemainder_spec hn hs
    (Finset.mem_powerset.mp hsubset)).2.2
  unfold primaryFactorRemainder at hprod
  rw [hprod]

/-- The original finite support is kept as an exact product predicate.
There is no coprimality assumption or replacement of its sharp cutoff. -/
theorem roughProduct_finite_factor_pairs (S : Finset Eisenstein) (X : ℝ)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ S, (roughProduct ψ w n:ℂ)*K n) =
      ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
        if d*e ∈ S then cutoffMoebius ψ w d*K (d*e) else 0 := by
  calc
    _ = ∑ n ∈ S,
        ∑ q ∈ ((primaryElementBall X).product (primaryElementBall X)).filter
          (fun q => q.1*q.2 = n), cutoffMoebius ψ w q.1*K (q.1*q.2) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact roughProduct_primary_factor_pair (hS n hn).1 (hS n hn).2.1
        (hS n hn).2.2 ψ w K
    _ = _ := primary_pair_fiber_support S X (fun d e => cutoffMoebius ψ w d*K (d*e))

end CubicFirstMoment

end

end OAI
