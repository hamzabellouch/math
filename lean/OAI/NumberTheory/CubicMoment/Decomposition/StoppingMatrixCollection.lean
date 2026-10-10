import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCoefficients
import OAI.NumberTheory.CubicMoment.Estimates.SparseStoppingLabels
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedPrimePredicate

namespace OAI

/-! Exact collection of the stopping-label factor sums into the actual
independent alpha and beta. The original product kernel is retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem stopping_matrix_collection (ρ X Z Q : ℝ) (h : ℕ) (early : Bool)
    (R D E U : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ q ∈ stoppingLabelBox ρ X, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
      ∑ e ∈ E, ∑ u ∈ U, ∑ r ∈ R, ∑ d ∈ D,
        if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
              q.1 q.2.1 h Z Q early r d ∧
            stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
          v r*cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (r*(d*e)*u) else 0) =
    ∑ q ∈ stoppingLabelBox ρ X, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
      ∑ a ∈ primaryPairSupport E U, ∑ b ∈ primaryPairSupport R D,
        stoppedAlpha E U ψ w
            (stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2) a *
          stoppedBeta R D v ψ w
            (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
              q.1 q.2.1 h Z Q early) b * K (a*b) := by
  apply Finset.sum_congr rfl
  intro q _hq
  congr 1
  rw [stopped_coefficients_sum]
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro e _he
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro r _hr
  apply Finset.sum_congr rfl
  intro d _hd
  have hmul : (e*u)*(r*d) = r*(d*e)*u := by ring
  rw [hmul]
  by_cases hs : stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      q.1 q.2.1 h Z Q early r d
  · by_cases he : stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e
    · simp only [hs,he,and_self,ite_true]
      ring
    · simp only [hs,he,and_false,false_and,ite_false]
  · simp only [hs,and_false,false_and,ite_false]

end CubicFirstMoment

end

end OAI
