import OAI.Probability.InvariantIsing.Haar.HaarContinuousDerivative
import OAI.Probability.InvariantIsing.Haar.HaarPolynomialGamma

namespace OAI

/-! Integration by parts for the logarithm of a positive polynomial on SO(N). -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
open scoped BigOperators
namespace InvariantIsing

theorem integral_haar_laplacian_log {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (p : MatrixPolynomial N)
    (hp : ∀ U : SpecialOrthogonal N, 0 < haarPolynomialValue p U) :
    (∫ U, haarPolynomialValue (haarPolynomialLaplacian N p) U*Real.log (haarPolynomialValue p U) ∂μ) =
      -(∫ U, haarPolynomialValue (haarPolynomialGamma p p) U/haarPolynomialValue p U ∂μ) := by
  let D (i j : Fin N) := matrixPolynomialDerivation (planeGenerator i j)
  let R (i j : Fin N) (U : SpecialOrthogonal N) :=
    haarPolynomialValue (D i j (D i j p)) U*Real.log (haarPolynomialValue p U)+
      (haarPolynomialValue (D i j p) U)^2/haarPolynomialValue p U
  have hlog : Continuous (fun U : SpecialOrthogonal N => Real.log (haarPolynomialValue p U)) :=
    (continuous_haarPolynomialValue p).log (fun U => (hp U).ne')
  have hR (i j : Fin N) : Continuous (R i j) :=
    ((continuous_haarPolynomialValue _).mul hlog).add
      (((continuous_haarPolynomialValue _).pow 2).div (continuous_haarPolynomialValue p)
        (fun U => (hp U).ne'))
  have hz (i j : Fin N) : (∫ U, R i j U ∂μ) = 0 := by
    apply integral_haar_continuous_derivative μ i j
      (fun U => haarPolynomialValue (D i j p) U*Real.log (haarPolynomialValue p U))
      (R i j) ((continuous_haarPolynomialValue _).mul hlog) (hR i j)
    intro U t
    have hq := hasDerivAt_specialPlaneRotation_polynomial (D i j p) i j U t
    have hpp := hasDerivAt_specialPlaneRotation_polynomial p i j U t
    convert hq.mul (hpp.log (hp (specialPlaneRotation i j t*U)).ne') using 1
    · rfl
    · dsimp only [R,D,haarPolynomialValue]
      ring
  have hs : (∫ U, ∑ i, ∑ j, R i j U ∂μ) = 0 := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => continuous_haar_integrable μ _ (hR i j)))]
    apply Finset.sum_eq_zero
    intro i _
    rw [integral_finsetSum _ (fun j _ => continuous_haar_integrable μ _ (hR i j))]
    simp only [hz,Finset.sum_const_zero]
  have he (U : SpecialOrthogonal N) : (∑ i, ∑ j, R i j U) =
      haarPolynomialValue (haarPolynomialLaplacian N p) U*Real.log (haarPolynomialValue p U)+
        haarPolynomialValue (haarPolynomialGamma p p) U/haarPolynomialValue p U := by
    simp only [R,D,haarPolynomialValue,haarPolynomialLaplacian_apply,haarPolynomialGamma,
      map_sum,map_mul,Finset.sum_add_distrib,Finset.sum_mul,Finset.sum_div,pow_two]
  simp_rw [he] at hs
  have hi1 : Integrable (fun U => haarPolynomialValue (haarPolynomialLaplacian N p) U*
      Real.log (haarPolynomialValue p U)) μ :=
    continuous_haar_integrable μ _ ((continuous_haarPolynomialValue _).mul hlog)
  have hi2 : Integrable (fun U => haarPolynomialValue (haarPolynomialGamma p p) U/
      haarPolynomialValue p U) μ := continuous_haar_integrable μ _
    ((continuous_haarPolynomialValue _).div (continuous_haarPolynomialValue _) (fun U => (hp U).ne'))
  rw [integral_add hi1 hi2] at hs
  exact eq_neg_of_add_eq_zero_left hs

end InvariantIsing

end

end OAI
