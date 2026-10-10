import OAI.NumberTheory.CubicMoment.Estimates.PrimeTailProductMean
import OAI.NumberTheory.CubicMoment.Angular.AngularPrimeProductPolynomialBounds

namespace OAI

/-! Full Mellin envelope for the actual fixed-angular prime polynomial. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem angular_fullPrimeProductSmoothed_height_mean (ℓ : ℤ) {R : ℝ} (hR : 0 ≤ R)
    (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ) (XA : κ → ℝ) (XB : ι → ℝ)
    (hXA : ∀ i, 0 < XA i) (hXB : ∀ i, 0 < XB i)
    (hAlo : ∀ i x, x < 1 → WA i x = 0) (hAhi : ∀ i x, R < x → WA i x = 0)
    (hBlo : ∀ i x, x < 1 → WB i x = 0) (hBhi : ∀ i x, R < x → WB i x = 0)
    (hWA : ∀ i x, ‖WA i x‖ ≤ 1) (hWB : ∀ i x, ‖WB i x‖ ≤ 1)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {X E V T : ℝ} (hX : 0 < X) (hE : 0 ≤ E)
    (hV : 0 < V) (hT : 0 < T) (n : ℕ)
    (hsmall : ∀ u, |u| ≤ V →
      dyadicHeightMean (fun t => ‖fullAngularPrimeProductGauss ℓ R WA WB XA XB (u+t)‖) T ≤ E) :
    dyadicHeightMean (fun t => ‖productGaussSmoothed
      (fullSquarefreePrimeSupport R WA XA 1) (fullSquarefreePrimeSupport R WB XB 1)
      (fullPrimeCoefficient R WA XA) (fullPrimeCoefficient R WB XB) ℓ W X t‖) T ≤
      E*zeroLineMellinMass W+
        (2*(primeCoefficientMassConstant R (Fintype.card κ)*
          primeCoefficientMassConstant R (Fintype.card ι)*(∏ i, XA i)*(∏ i, XB i)))/V^n*
            zeroLineMellinMoment W n := by
  have he (u : ℝ) : productGaussPolynomial
      (fullSquarefreePrimeSupport R WA XA 1) (fullSquarefreePrimeSupport R WB XB 1)
      (fullPrimeCoefficient R WA XA) (fullPrimeCoefficient R WB XB) ℓ u =
      fullAngularPrimeProductGauss ℓ R WA WB XA XB u := by
    rfl
  have hpA : 0 ≤ ∏ i, XA i := (Finset.prod_pos (fun i _ => hXA i)).le
  have hpB : 0 ≤ ∏ i, XB i := (Finset.prod_pos (fun i _ => hXB i)).le
  apply productGaussSmoothed_height_mean _ _ _ _
    (fun a ha => (fullSquarefreePrimeSupport_primary R WA XA 1 ha).1)
    (fun b hb => (fullSquarefreePrimeSupport_primary R WB XB 1 hb).1)
    ℓ W hW hpos hsm hX (by unfold primeCoefficientMassConstant; positivity) hE hV hT _ n _
  · intro u
    rw [he]
    simpa only [mul_assoc] using fullAngularPrimeProductGauss_bound ℓ hR WA WB XA XB hXA hXB hAlo hAhi hBlo hBhi hWA hWB u
  · intro u hu
    simp_rw [he]
    simpa only [add_comm] using hsmall u hu

end CubicFirstMoment

end

end OAI
