import OAI.NumberTheory.CubicMoment.Estimates.ShortConvolutionExpansion
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryWeightedConvolution

namespace OAI

/-! Exact short-factor decomposition of the original finite von Mangoldt
convolution, including its global norm weight and arbitrary character. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def shortBranchScalar (S : Finset ι) : ℂ :=
  (-1)^S.card * 2^(Fintype.card ι-S.card)

theorem primaryPrimeWeight_expansion (χ : Eisenstein → ℂ) (V : ℝ → ℂ)
    {Y : ℝ} (hY : 0 < Y) :
    primaryConvolutionPolynomial (fun _ : ι => idealVonMangoldt) χ V Y =
      ∑ S : Finset ι, shortBranchScalar S*
        primaryConvolutionPolynomial (shortBranchFactor (2*Y) S) χ V Y := by
  calc
    _ = ∑ b ∈ primaryElementBall (2*Y), ∑ S : Finset ι,
        shortBranchScalar S*((MvPowerSeries.coeff (idealExponentOf b)
          (∏ i, shortBranchFactor (2*Y) S i):ℝ):ℂ)*χ b*V (norm b/Y) := by
      unfold primaryConvolutionPolynomial
      apply Finset.sum_congr rfl
      intro b hb
      have hb' := mem_primaryElementBall.mp hb
      have hN : idealExponentNorm (idealExponentOf b) ≤ 2*Y := by
        simpa only [idealExponentOf_norm (primary_ne_zero hb'.1)] using hb'.2
      rw [short_prime_product_expansion (ι := ι) (by positivity : 0 ≤ 2*Y) _ hN,
        Complex.ofReal_sum,Finset.sum_mul,Finset.sum_mul]
      simp only [Finset.powerset_univ,shortBranchScalar,Complex.ofReal_mul,Complex.ofReal_pow,
        Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      unfold primaryConvolutionPolynomial
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

end CubicFirstMoment

end

end OAI
