import OAI.Geometry.RCD.Sobolev.ScaledGammaBound
import OAI.Geometry.RCD.Coordinates.NormalizedProductError

namespace OAI

/-! # The scaled cutoff commutator vanishes with its value error -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem scaled_weighted_gamma_error_tendsto (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (Ω : ℕ → Set X) [∀ k, IsFiniteMeasure (μ.restrict (Ω k))]
    (hmass : ∀ k, 0<μ.real (Ω k)) (r : ℕ → ℝ) (hr : ∀ k, 0≤r k)
    (f g : ℕ → SobolevSpace μ hQ) (z v : ℕ → X → ℝ)
    {M L B : ℝ} (hM : 0≤M) (hL : 0≤L) (hB : 0≤B)
    (hf : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k), r k^2*localGamma μ hQ (f k) (f k) x≤M^2)
    (hg : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k), r k^2*localGamma μ hQ (g k) (g k) x≤L^2)
    (hv : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k), |v k x|≤B)
    (hz : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k), |z k x|≤δ) :
    Tendsto (fun k => r k^2*(μ.real (Ω k))⁻¹*
      ∫ x in Ω k, v k x*z k x*localGamma μ hQ (f k) (g k) x ∂μ) atTop (𝓝 0) := by
  have hmass' (k : ℕ) : 0<(μ.restrict (Ω k)).real univ := by
    simpa only [Measure.real,Measure.restrict_apply_univ] using hmass k
  have hb : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k),
      |v k x*(r k^2*localGamma μ hQ (f k) (g k) x)|≤B*(M*L) := by
    filter_upwards [hf,hg,hv] with k hfk hgk hvk
    filter_upwards [scaled_gamma_bound μ hQ (f k) (g k) (hr k) hM hL hfk hgk,hvk]
      with x hx hvx
    rw [abs_mul]
    exact mul_le_mul hvx hx (abs_nonneg _) hB
  have ht := normalized_product_error_tendsto (fun k => μ.restrict (Ω k)) hmass'
    z (fun k x => v k x*(r k^2*localGamma μ hQ (f k) (g k) x))
    (mul_nonneg hB (mul_nonneg hM hL)) hb hz
  convert ht using 1
  funext k
  simp only [Measure.real,Measure.restrict_apply_univ]
  have he : (fun x => z k x*(v k x*(r k^2*localGamma μ hQ (f k) (g k) x)))=
      fun x => r k^2*(v k x*z k x*localGamma μ hQ (f k) (g k) x) := by
    funext x
    ring
  rw [he,integral_const_mul]
  ring

end RegularPointCoordinates

end

end OAI
