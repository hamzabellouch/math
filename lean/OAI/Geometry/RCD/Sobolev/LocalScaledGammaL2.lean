import OAI.Geometry.RCD.Sobolev.LocalScaledGammaDifference

namespace OAI

/-! # The original normalization controls the squared energy-density error -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem local_scaled_gamma_l2_tendsto (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (Ω : ℕ → Set X) (r c : ℕ → ℝ) (hr : ∀ k, 0<r k) (hc : ∀ k, 0≤c k)
    {M Q : ℝ} (hM : 0≤M) (hQ0 : 0≤Q) (f g : ℕ → SobolevSpace μ hQ)
    (hf : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k), r k^2*localGamma μ hQ (f k) (f k) x≤M^2)
    (hg : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k), r k^2*localGamma μ hQ (g k) (g k) x≤Q^2)
    (hlim : Tendsto (fun k => c k*r k^2*∫ x in Ω k, localGamma μ hQ (f k-g k) (f k-g k) x ∂μ)
      atTop (𝓝 0)) :
    Tendsto (fun k => c k*∫ x in Ω k,
      (r k^2*(localGamma μ hQ (f k) (f k) x-localGamma μ hQ (g k) (g k) x))^2 ∂μ)
      atTop (𝓝 0) := by
  have hupper : ∀ᶠ k in atTop,
      c k*(∫ x in Ω k, (r k^2*(localGamma μ hQ (f k) (f k) x-localGamma μ hQ (g k) (g k) x))^2 ∂μ)≤
        (M+Q)^2*(c k*r k^2*∫ x in Ω k, localGamma μ hQ (f k-g k) (f k-g k) x ∂μ) := by
    filter_upwards [hf,hg] with k hfk hgk
    have hp := local_scaled_gamma_difference_sq_le μ hQ (hr k) hM hQ0 (f k) (g k) hfk hgk
    have hir : Integrable (fun x => (M+Q)^2*(r k^2*localGamma μ hQ (f k-g k) (f k-g k) x)) (μ.restrict (Ω k)) :=
      (((localGamma_memL1 μ hQ (f k-g k) (f k-g k)).restrict).const_mul (r k^2)).const_mul ((M+Q)^2)
    have hsm : AEStronglyMeasurable (fun x => (r k^2*(localGamma μ hQ (f k) (f k) x-
        localGamma μ hQ (g k) (g k) x))^2) (μ.restrict (Ω k)) :=
      ((((localGamma_memL1 μ hQ (f k) (f k)).aestronglyMeasurable.sub
      (localGamma_memL1 μ hQ (g k) (g k)).aestronglyMeasurable).const_mul (r k^2)).pow 2).restrict
    have hil := hir.mono' hsm (hp.mono fun x hx => by
      simpa only [Real.norm_eq_abs,abs_pow,sq_abs] using hx)
    have hi := mul_le_mul_of_nonneg_left (integral_mono_ae hil hir hp) (hc k)
    simp only [integral_const_mul] at hi
    convert hi using 1; ring
  apply squeeze_zero' (Eventually.of_forall fun k => mul_nonneg (hc k) (integral_nonneg fun x => sq_nonneg _)) hupper
  simpa only [mul_zero] using hlim.const_mul ((M+Q)^2)

end RegularPointCoordinates

end

end OAI
