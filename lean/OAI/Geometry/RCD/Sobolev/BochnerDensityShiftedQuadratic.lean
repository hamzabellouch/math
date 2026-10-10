import OAI.Geometry.RCD.Sobolev.LocalBochnerDensityProduct
import OAI.Geometry.RCD.Sobolev.FiniteDimensionalBochnerAE

namespace OAI

/-! # The shifted directional bound from full products and scalar dimensional Bochner -/

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [SigmaFinite μ] {m : ℕ}

/-- The three product identities for a direction and its square imply
the sharp bound for the first Hessian action. The positive form is the
actual density of the same full Bochner measure. -/
theorem bochner_measure_shifted_quadratic_bound (M : PositiveBilinearMeasure X (Euclidean m))
    (v w z : Euclidean m) (χ : X →ᵇ ℝ) (Hv Hw Hz s : X → ℝ)
    (D : X → Euclidean m →ₗ[ℝ] ℝ) (N b : ℝ) (hN : 0<N)
    (hHv : Integrable Hv μ) (hHw : Integrable Hw μ) (hHz : Integrable Hz μ)
    {S : Set X} (hS : MeasurableSet S)
    (hvz : (M.bilinear v z).restrict S=
      (signedSourceWeight (M.bilinear v w) χ+signedSourceWeight (M.bilinear v w) χ+
        (2 : ℝ) • μ.withDensityᵥ Hv).restrict S)
    (hwz : (M.bilinear w z).restrict S=
      (signedSourceWeight (M.bilinear w w) χ+signedSourceWeight (M.bilinear w w) χ+
        (2 : ℝ) • μ.withDensityᵥ Hw).restrict S)
    (hzz : (M.bilinear z z).restrict S=
      (signedSourceWeight (M.bilinear z w) χ+signedSourceWeight (M.bilinear z w) χ+
        (2 : ℝ) • μ.withDensityᵥ Hz).restrict S)
    (hsquare : Hz =ᵐ[μ.restrict S] fun x => 2*χ x*Hw x+2*(s x)^2)
    (hdelta : ∀ᵐ x ∂μ.restrict S, D x z=2*χ x*D x w+2*s x)
    (hBE : ∀ a, ∀ᵐ x ∂μ.restrict S, (D x a)^2≤N*bochnerRadonDensity μ M x a a) :
    ∀ᵐ x ∂μ.restrict S, (Hv x-b*s x)^2≤
      (bochnerRadonDensity μ M x v v-2*b*D x v+N*b^2)*(s x)^2 := by
  have h₁ := signed_rnDeriv_local_product μ (M.bilinear v w) (M.bilinear v w)
    (M.bilinear v z) χ χ hHv hS hvz
  have h₂ := signed_rnDeriv_local_product μ (M.bilinear w w) (M.bilinear w w)
    (M.bilinear w z) χ χ hHw hS hwz
  have h₃ := signed_rnDeriv_local_product μ (M.bilinear z w) (M.bilinear z w)
    (M.bilinear z z) χ χ hHz hS hzz
  have hshift := ae_finite_bochner_shift_nonneg (μ.restrict S) (bochnerRadonDensity μ M) D N hN hBE
  filter_upwards [hshift,h₁,h₂,h₃,hsquare,hdelta,
    ae_restrict_of_ae (bochnerRadonDensity_rep μ M v z),
    ae_restrict_of_ae (bochnerRadonDensity_rep μ M v w),
    ae_restrict_of_ae (bochnerRadonDensity_rep μ M w z),
    ae_restrict_of_ae (bochnerRadonDensity_rep μ M w w),
    ae_restrict_of_ae (bochnerRadonDensity_rep μ M z z),
    ae_restrict_of_ae (bochnerRadonDensity_rep μ M z w)] with x hp h₁ h₂ h₃ hs hd hvz hvw hwz hww hzz hzw
  rw [hvz,hvw] at h₁
  rw [hwz,hww] at h₂
  rw [hzz,hzw,hs,bochnerRadonDensity_symmetric μ M x z w] at h₃
  let B := bochnerRadonDensity μ M x
  have hf : B v z=2*χ x*B v w+2*Hv x := by
    change B v z=χ x*B v w+χ x*B v w+2*Hv x at h₁
    linarith only [h₁]
  have hg : B w z=2*χ x*B w w+2*Hw x := by
    change B w z=χ x*B w w+χ x*B w w+2*Hw x at h₂
    linarith only [h₂]
  have hq : B z z=4*(χ x)^2*B w w+8*χ x*Hw x+4*(s x)^2 := by
    change B z z=χ x*B w z+χ x*B w z+2*(2*χ x*Hw x+2*(s x)^2) at h₃
    rw [hg] at h₃
    nlinarith only [h₃]
  exact bochner_shifted_quadratic_perturbation_bound B (D x) N
    (bochnerRadonDensity_symmetric μ M x) hp
    v w z (χ x) (s x) (Hv x) (Hw x) b hf hg hq hd

end RegularPointCoordinates

end

end OAI
