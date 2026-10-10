import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedCoefficients

namespace OAI

/-! Exact collection of the literal stopped beta into its ordered prime
tuples and independent selected divisor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_distinguished_tuple_sum (S : ι → Finset Eisenstein)
    (W : ι → Eisenstein → ℂ) (ψ : ℝ → ℝ) (w z : ℝ) (D : Finset Eisenstein)
    (selected : Eisenstein → Eisenstein → Prop) (K : Eisenstein → ℂ) :
    (∑ n ∈ primaryPairSupport (orderedConvolutionSupport S) D,
      stoppedBeta (orderedConvolutionSupport S) D (distinguishedTupleCoefficient S W ψ w z)
        ψ w selected n*K n) =
    ((Fintype.card ι).factorial:ℂ)⁻¹ *
      ∑ d ∈ D, ∑ f ∈ Fintype.piFinset S,
        if selected (∏ i, f i) d then
          (∏ i, W i (f i)*distinguishedPrimeWeight ψ w z (f i))*
            cutoffMoebius ψ w d*K ((∏ i, f i)*d) else 0 := by
  unfold stoppedBeta
  rw [primaryPairCoefficient_sum,Finset.sum_product]
  calc
    _ = ((Fintype.card ι).factorial:ℂ)⁻¹ *
        ∑ r ∈ orderedConvolutionSupport S,
          orderedConvolution S (fun i p => W i p*distinguishedPrimeWeight ψ w z p) r *
            ∑ d ∈ D, if selected r d then cutoffMoebius ψ w d*K (r*d) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hs : selected r d
      · simp only [hs,ite_true,distinguishedTupleCoefficient]
        ring
      · simp only [hs,ite_false,zero_mul,mul_zero]
    _ = _ := by
      rw [orderedConvolution_sum]
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hs : selected (∏ i, f i) d
      · simp only [hs,ite_true]
        ring
      · simp only [hs,ite_false,mul_zero]

end CubicFirstMoment

end

end OAI
