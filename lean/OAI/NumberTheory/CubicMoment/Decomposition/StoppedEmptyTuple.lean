import OAI.NumberTheory.CubicMoment.Decomposition.StoppedLargestRoles

namespace OAI

/-! With no distinguished prime coordinates, the largest prime can only
occur in the selected divisor. This removes an artificial nonempty-tuple
restriction from the stopped-coefficient sequence estimate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [IsEmpty ι]

theorem stopped_distinguished_empty (B ρ a b w z u : ℝ)
    {j : ℕ} (hj : j < geometricBinCount ρ B) (j₀ k h : ℕ)
    (Z Q : ℝ) (early : Bool) (W : ι → ℝ → ℂ)
    (D : Finset Eisenstein) (hD : ∀ d ∈ D, primary d) (v e : Eisenstein) :
    (∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D,
      stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D
        (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
          (fun l p => W l (norm p)) primeDetectorCutoff w z) primeDetectorCutoff w
        (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*cubicSymbol n v else 0)) = 0 := by
  rw [stoppedBeta_distinguished_original_tuple]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro f hf
  simp only [Finset.prod_of_isEmpty,one_mul]
  split_ifs with hdiv htest
  · have hp := largestPrimeChoice_prime_of_bin hj (hD d hd) htest.2.2.2
    exact (hp.1.2.not_isUnit (isUnit_of_dvd_one hdiv)).elim
  · rfl
  · rfl

end CubicFirstMoment

end

end OAI
