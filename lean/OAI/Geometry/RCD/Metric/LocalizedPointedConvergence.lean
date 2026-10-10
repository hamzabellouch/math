import OAI.Geometry.RCD.Metric.PointedLimitCompatibility
import OAI.Geometry.RCD.Coordinates.NormalizedUniformMean

namespace OAI

/-! # Compactly supported tests of local pointed value convergence

A fixed gap between the test support and the convergence ball absorbs the
metric approximation error. The estimate holds on the whole outer ball.
-/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem localized_pointed_uniform_convergence (μ : Measure X)
    {n : ℕ} {S ρ τ B : ℝ} (hB : 0≤B) (hρτ : ρ<τ) (_hτS : τ≤S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (u : ℕ → X → ℝ) (g ψ : Euclidean n → ℝ)
    (hψ : ∀ z, |ψ z|≤B) (hψ0 : ∀ z, ρ≤‖z‖ → ψ z=0)
    (hconv : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop,
      ∀ᵐ x ∂μ.restrict (ball (p k) (τ*r k)), |u k x-g (v k x)|≤η) :
    ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (ball (p k) (S*r k)),
      |ψ (v k x)*(u k x-g (v k x))|≤η := by
  intro η hη
  let δ := η/(B+1)
  have hδ : 0<δ := div_pos hη (by linarith)
  have hBδ : B*δ≤η := by
    have he : (B+1)*δ=η := by dsimp only [δ]; field_simp
    nlinarith
  filter_upwards [hconv δ hδ,
    hεlim.eventually (Iio_mem_nhds (show 0<(τ-ρ)/3 by linarith))] with k hk he
  rw [ae_restrict_iff' measurableSet_ball] at hk
  filter_upwards [ae_restrict_of_ae hk,ae_restrict_mem measurableSet_ball] with x hx hball
  by_cases hi : x∈ball (p k) (τ*r k)
  · rw [abs_mul]
    exact (mul_le_mul (hψ _) (hx hi) (abs_nonneg _) hB).trans hBδ
  · have hout : dist x (p k)≤S*r k := (show dist x (p k)<S*r k from hball).le
    have hτ : τ≤dist x (p k)/r k := by
      apply (le_div_iff₀ (hr k)).mpr
      exact le_of_not_gt hi
    have hSp : 0≤S*r k := (dist_nonneg : 0≤dist x (p k)).trans hout
    have hab := (abs_le.mp ((hv k).2.1 x (p k) hout
      (by simpa only [dist_self] using hSp))).1
    have ht := dist_triangle (v k x) 0 (v k (p k))
    have hc := (hv k).1
    rw [dist_comm 0 (v k (p k))] at ht
    simp only [dist_zero_right] at ht hc
    have hnorm : ρ≤‖v k x‖ := by linarith
    rw [hψ0 _ hnorm,zero_mul,abs_zero]
    exact hη.le

end RegularPointCoordinates

end

end OAI
