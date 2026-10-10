import OAI.Geometry.RCD.Sobolev.PoissonCutoffErrors
import OAI.Geometry.RCD.Metric.ContainingMassL2Error

namespace OAI

/-! # The cutoff errors need only normalized L2 convergence in value -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem containing_mass_source_l2_error_tendsto (μ : ℕ → Measure X)
    [∀ k, IsFiniteMeasure (μ k)] (m : ℕ → ℝ) (hmass : ∀ k, 0 < m k)
    (hmass_le : ∀ k, (μ k).real univ ≤ m k)
    (z v : ℕ → X → ℝ) (a : ℕ → ℝ) {A B : ℝ} (hA : 0≤A)
    (ha : ∀ᶠ k in atTop, |a k|≤A)
    (hv : ∀ᶠ k in atTop, ∀ᵐ x ∂μ k, |v k x|≤B)
    (hzm : ∀ k, MemLp (z k) 2 (μ k))
    (hvm : ∀ k, AEStronglyMeasurable (v k) (μ k))
    (hz : Tendsto (fun k => (m k)⁻¹*∫ x, (z k x)^2 ∂μ k) atTop (𝓝 0)) :
    Tendsto (fun k => a k*(m k)⁻¹*
      ∫ x, (v k x)^2*z k x ∂μ k) atTop (𝓝 0) := by
  have hb : ∀ᶠ k in atTop, ∀ᵐ x ∂μ k, |a k*(v k x)^2|≤A*B^2 := by
    filter_upwards [ha,hv] with k hak hvk
    filter_upwards [hvk] with x hvx
    rw [abs_mul,abs_pow]
    exact mul_le_mul hak (pow_le_pow_left₀ (abs_nonneg _) hvx 2) (sq_nonneg _) hA
  have ht := l2_product_error_of_containing_mass μ m hmass hmass_le z (fun k x => a k*(v k x)^2)
    hzm (fun k => ((hvm k).pow 2).const_mul (a k)) hb hz
  convert ht using 1
  funext k
  have he : (fun x => z k x*(a k*(v k x)^2))=fun x => a k*((v k x)^2*z k x) := by
    funext x
    ring
  rw [he,integral_const_mul]
  ring


variable [MetricSpace X] [BorelSpace X] [ProperSpace X]

theorem containing_mass_gamma_l2_error_tendsto (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (Ω : ℕ → Set X) [∀ k, IsFiniteMeasure (μ.restrict (Ω k))]
    (m : ℕ → ℝ) (hmass : ∀ k, 0 < m k)
    (hmass_le : ∀ k, μ.real (Ω k) ≤ m k) (r : ℕ → ℝ) (hr : ∀ k, 0≤r k)
    (f g : ℕ → SobolevSpace μ hQ) (z v : ℕ → X → ℝ)
    {M L B : ℝ} (hM : 0≤M) (hL : 0≤L) (hB : 0≤B)
    (hf : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k), r k^2*localGamma μ hQ (f k) (f k) x≤M^2)
    (hg : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k), r k^2*localGamma μ hQ (g k) (g k) x≤L^2)
    (hv : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k), |v k x|≤B)
    (hzm : ∀ k, MemLp (z k) 2 (μ.restrict (Ω k)))
    (hvm : ∀ k, AEStronglyMeasurable (v k) (μ.restrict (Ω k)))
    (hz : Tendsto (fun k => (m k)⁻¹*∫ x in Ω k, (z k x)^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => r k^2*(m k)⁻¹*
      ∫ x in Ω k, v k x*z k x*localGamma μ hQ (f k) (g k) x ∂μ) atTop (𝓝 0) := by
  have hb : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k),
      |v k x*(r k^2*localGamma μ hQ (f k) (g k) x)|≤B*(M*L) := by
    filter_upwards [hf,hg,hv] with k hfk hgk hvk
    filter_upwards [scaled_gamma_bound μ hQ (f k) (g k) (hr k) hM hL hfk hgk,hvk]
      with x hx hvx
    rw [abs_mul]
    exact mul_le_mul hvx hx (abs_nonneg _) hB
  have ht := l2_product_error_of_containing_mass (fun k => μ.restrict (Ω k)) m hmass
    (fun k => by simpa only [Measure.real,Measure.restrict_apply_univ] using hmass_le k)
    z (fun k x => v k x*(r k^2*localGamma μ hQ (f k) (g k) x))
    hzm (fun k => (hvm k).mul
      (((localGamma_memL1 μ hQ (f k) (g k)).restrict.aestronglyMeasurable).const_mul (r k^2)))
    hb (by simpa only [Measure.real,Measure.restrict_apply_univ] using hz)
  convert ht using 1
  funext k
  have he : (fun x => z k x*(v k x*(r k^2*localGamma μ hQ (f k) (g k) x)))=
      fun x => r k^2*(v k x*z k x*localGamma μ hQ (f k) (g k) x) := by
    funext x
    ring
  rw [he,integral_const_mul]
  ring


end RegularPointCoordinates

end

end OAI
