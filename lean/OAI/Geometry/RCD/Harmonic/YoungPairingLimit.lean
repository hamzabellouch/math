import OAI.Geometry.RCD.Sobolev.WeightedGammaYoung

namespace OAI

/-! # Vanishing gradient error controls mixed pairings -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem tendsto_zero_of_young {a e : ℕ → ℝ} {C : ℝ} (hC : 0≤C)
    (he : Tendsto e atTop (𝓝 0))
    (hbound : ∀ t : ℝ, 0<t → ∀ᶠ k in atTop, 2*t*|a k|≤e k+t^2*C) :
    Tendsto a atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  let t := δ/(C+1)
  have ht : 0<t := div_pos hδ (by positivity)
  have hid : t*(C+1)=δ := by
    dsimp only [t]
    exact div_mul_cancel₀ δ (by positivity : C+1≠0)
  have htc : t*C<δ := by nlinarith
  filter_upwards [hbound t ht,he.eventually (Iio_mem_nhds (mul_pos ht hδ))] with k hk hek
  rw [Real.dist_eq,sub_zero]
  nlinarith [mul_lt_mul_of_pos_left htc ht]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem cutoff_mixed_error_tendsto (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (Ω : ℕ → Set X) (c : ℕ → ℝ) (hc : ∀ k, 0≤c k)
    (f g : ℕ → SobolevSpace μ hQ) (φ χ : ℕ → X → ℝ)
    {B C D : ℝ} (hB : 0≤B) (hC : 0≤C)
    (hφ : ∀ k, AEStronglyMeasurable (φ k) (μ.restrict (Ω k)))
    (hχ : ∀ k, AEStronglyMeasurable (χ k) (μ.restrict (Ω k)))
    (hφb : ∀ k, ∀ᵐ x ∂μ.restrict (Ω k), |φ k x|≤D)
    (hχb : ∀ k, ∀ᵐ x ∂μ.restrict (Ω k), |χ k x|≤1)
    (hdom : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k), |φ k x|≤B*|χ k x|)
    (henergy : ∀ᶠ k in atTop, c k*(∫ x in Ω k, localGamma μ hQ (g k) (g k) x ∂μ)≤C)
    (herror : Tendsto (fun k => c k*∫ x in Ω k, (χ k x)^2*
      localGamma μ hQ (f k) (f k) x ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => c k*∫ x in Ω k, φ k x*localGamma μ hQ (f k) (g k) x ∂μ)
      atTop (𝓝 0) := by
  apply tendsto_zero_of_young (C := B^2*C) (mul_nonneg (sq_nonneg _) hC) herror
  intro t ht
  filter_upwards [hdom,henergy] with k hdomk hek
  have h := weighted_gamma_young_integral μ hQ (f k) (g k) hB ht.le
    (hφ k) (hχ k) (hφb k) (hχb k) hdomk
  have hh := mul_le_mul_of_nonneg_left h (hc k)
  have he := mul_le_mul_of_nonneg_left hek (mul_nonneg (sq_nonneg t) (sq_nonneg B))
  rw [abs_mul,abs_of_nonneg (hc k)]
  nlinarith only [hh,he]

end RegularPointCoordinates

end

end OAI
