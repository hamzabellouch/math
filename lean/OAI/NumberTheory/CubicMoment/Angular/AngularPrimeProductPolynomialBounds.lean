import OAI.NumberTheory.CubicMoment.Decomposition.PrimeProductPolynomialBounds
import OAI.NumberTheory.CubicMoment.Estimates.PrimeTailProductMellin

namespace OAI

/-! The literal angular Gauss product and its coefficient-mass bound. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma theta_coefficient_energy (ℓ : ℤ) (S : Finset Eisenstein)
    (α : Eisenstein → ℂ) (hS : ∀ b ∈ S, primary b) :
    (∑ b ∈ S, ‖theta ℓ b*α b‖^2) = ∑ b ∈ S, ‖α b‖^2 := by
  apply Finset.sum_congr rfl
  intro b hb
  rw [norm_theta_mul (primary_ne_zero (hS b hb))]

def fullAngularPrimeProductGauss (ℓ : ℤ) (R : ℝ) (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ)
    (XA : κ → ℝ) (XB : ι → ℝ) (u : ℝ) : ℂ :=
  productGaussPolynomial (fullSquarefreePrimeSupport R WA XA 1)
    (fullSquarefreePrimeSupport R WB XB 1)
    (fullPrimeCoefficient R WA XA) (fullPrimeCoefficient R WB XB) ℓ u

lemma fullAngularPrimeProductGauss_bound (ℓ : ℤ) {R : ℝ} (hR : 0 ≤ R)
    (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ) (XA : κ → ℝ) (XB : ι → ℝ)
    (hXA : ∀ i, 0 < XA i) (hXB : ∀ i, 0 < XB i)
    (hAlo : ∀ i x, x < 1 → WA i x = 0) (hAhi : ∀ i x, R < x → WA i x = 0)
    (hBlo : ∀ i x, x < 1 → WB i x = 0) (hBhi : ∀ i x, R < x → WB i x = 0)
    (hWA : ∀ i x, ‖WA i x‖ ≤ 1) (hWB : ∀ i x, ‖WB i x‖ ≤ 1) (u : ℝ) :
    ‖fullAngularPrimeProductGauss ℓ R WA WB XA XB u‖ ≤
      (primeCoefficientMassConstant R (Fintype.card κ)*
        primeCoefficientMassConstant R (Fintype.card ι))*((∏ i, XA i)*(∏ i, XB i)) := by
  have hF (a : Eisenstein) (ha : a ∈ fullSquarefreePrimeSupport R WA XA 1)
      (b : Eisenstein) (hb : b ∈ fullSquarefreePrimeSupport R WB XB 1) :
      ‖theta ℓ (a*b)*gauss (a*b)*normTwist u (a*b)‖ ≤ 1 := by
    have hn : a*b ≠ 0 := mul_ne_zero
      (primary_ne_zero (fullSquarefreePrimeSupport_primary R WA XA 1 ha).1)
      (primary_ne_zero (fullSquarefreePrimeSupport_primary R WB XB 1 hb).1)
    simp only [norm_mul,norm_theta hn,norm_normTwist,one_mul,mul_one]
    exact norm_gauss_le_one (primary_mul (fullSquarefreePrimeSupport_primary R WA XA 1 ha).1
      (fullSquarefreePrimeSupport_primary R WB XB 1 hb).1)
  have h := fullPrimeProduct_weighted_bound R WA WB XA XB
    (fun a b => theta ℓ (a*b)*gauss (a*b)*normTwist u (a*b)) hF
  have hsame : (∑ a ∈ fullSquarefreePrimeSupport R WA XA 1,
      ∑ b ∈ fullSquarefreePrimeSupport R WB XB 1,
        fullPrimeCoefficient R WA XA a*fullPrimeCoefficient R WB XB b*
          (theta ℓ (a*b)*gauss (a*b)*normTwist u (a*b))) = fullAngularPrimeProductGauss ℓ R WA WB XA XB u := by
    simp only [fullAngularPrimeProductGauss,productGaussPolynomial,mul_assoc]
  rw [hsame,mul_one] at h
  apply h.trans
  apply (mul_le_mul (fullPrimeCoefficient_l1_unit hR WA XA hXA hAlo hAhi hWA 1)
    (fullPrimeCoefficient_l1_unit hR WB XB hXB hBlo hBhi hWB 1)
    (Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _))
    (by
      unfold primeCoefficientMassConstant
      exact mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => (hXA i).le)))).trans_eq
  ring


end CubicFirstMoment

end

end OAI
