import OAI.NumberTheory.CubicMoment.Estimates.PrimeTailProductMellin
import OAI.NumberTheory.CubicMoment.Decomposition.PrimeProductPolynomialBounds

namespace OAI

/-! A bounded-shift mean for the unsmoothed Gauss polynomial suffices
for its actual product envelope. All complementary Mellin frequencies are
paid for by an integrable moment, with no frequency discarded. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma zeroLineMellinMoment_nonneg (W : ℝ → ℂ) (n : ℕ) :
    0 ≤ zeroLineMellinMoment W n := by
  unfold zeroLineMellinMoment
  positivity

theorem productGaussSmoothed_height_mean (P S : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (hP : ∀ a ∈ P, primary a) (hS : ∀ b ∈ S, primary b)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X M B V T : ℝ} (hX : 0 < X) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hV : 0 < V) (hT : 0 < T)
    (hbound : ∀ u, ‖productGaussPolynomial P S α β ℓ u‖ ≤ M) (n : ℕ)
    (hsmall : ∀ u, |u| ≤ V →
      dyadicHeightMean (fun t => ‖productGaussPolynomial P S α β ℓ (t+u)‖) T ≤ B) :
    dyadicHeightMean (fun t => ‖productGaussSmoothed P S α β ℓ W X t‖) T ≤
      B*zeroLineMellinMass W+(2*M)/V^n*zeroLineMellinMoment W n := by
  exact zeroLineMellin_height_mean W hW hpos hsm hX
    (productGaussPolynomial_continuous P S α β ℓ)
    (productGaussSmoothed_continuous P S α β ℓ W X)
    (fun t => product_gauss_mellin P S α β hP hS ℓ W hW hpos hsm hX t)
    hM hB hV hT hbound n hsmall

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem fullPrimeProductSmoothed_height_mean {R : ℝ} (hR : 0 ≤ R)
    (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ) (XA : κ → ℝ) (XB : ι → ℝ)
    (hXA : ∀ i, 0 < XA i) (hXB : ∀ i, 0 < XB i)
    (hAlo : ∀ i x, x < 1 → WA i x = 0) (hAhi : ∀ i x, R < x → WA i x = 0)
    (hBlo : ∀ i x, x < 1 → WB i x = 0) (hBhi : ∀ i x, R < x → WB i x = 0)
    (hWA : ∀ i x, ‖WA i x‖ ≤ 1) (hWB : ∀ i x, ‖WB i x‖ ≤ 1)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X E V T : ℝ} (hX : 0 < X) (hE : 0 ≤ E)
    (hV : 0 < V) (hT : 0 < T) (n : ℕ)
    (hsmall : ∀ u, |u| ≤ V →
      dyadicHeightMean (fun t => ‖fullPrimeProductGauss R WA WB XA XB (u+t)‖) T ≤ E) :
    dyadicHeightMean (fun t => ‖productGaussSmoothed
      (fullSquarefreePrimeSupport R WA XA 1) (fullSquarefreePrimeSupport R WB XB 1)
      (fullPrimeCoefficient R WA XA) (fullPrimeCoefficient R WB XB) 0 W X t‖) T ≤
      E*zeroLineMellinMass W+
        (2*(primeCoefficientMassConstant R (Fintype.card κ)*
          primeCoefficientMassConstant R (Fintype.card ι)*(∏ i, XA i)*(∏ i, XB i)))/V^n*
            zeroLineMellinMoment W n := by
  have he (u : ℝ) : productGaussPolynomial
      (fullSquarefreePrimeSupport R WA XA 1) (fullSquarefreePrimeSupport R WB XB 1)
      (fullPrimeCoefficient R WA XA) (fullPrimeCoefficient R WB XB) 0 u =
      fullPrimeProductGauss R WA WB XA XB u := by
    simp only [productGaussPolynomial,fullPrimeProductGauss,theta_zero,mul_one]
  have hpA : 0 ≤ ∏ i, XA i := (Finset.prod_pos (fun i _ => hXA i)).le
  have hpB : 0 ≤ ∏ i, XB i := (Finset.prod_pos (fun i _ => hXB i)).le
  apply productGaussSmoothed_height_mean _ _ _ _
    (fun a ha => (fullSquarefreePrimeSupport_primary R WA XA 1 ha).1)
    (fun b hb => (fullSquarefreePrimeSupport_primary R WB XB 1 hb).1)
    0 W hW hpos hsm hX (by unfold primeCoefficientMassConstant; positivity) hE hV hT _ n _
  · intro u
    rw [he]
    simpa only [mul_assoc] using fullPrimeProductGauss_bound hR WA WB XA XB hXA hXB hAlo hAhi hBlo hBhi hWA hWB u
  · intro u hu
    simp_rw [he]
    simpa only [add_comm] using hsmall u hu

end CubicFirstMoment

end

end OAI
