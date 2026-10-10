import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.GaussianOffDiagonal
import OAI.Geometry.RCD.Sobolev.CutoffErrorEstimates

namespace OAI

/-! # Uniform small-time cutoff errors from local volume lower bounds -/

open Set Metric MeasureTheory Filter
open scoped Topology

noncomputable section

namespace RegularPointCoordinates

private theorem sqrt_power_inverse (n : ℕ) {t : ℝ} (ht : 0 < t) (V : ℝ) :
    V / (t⁻¹) ^ ((n : ℝ) / 2) = V * (Real.sqrt t) ^ n := by
  have hs : (Real.sqrt t) ^ n = t ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ht.le]
    congr 1
    ring
  rw [Real.inv_rpow ht.le, div_inv_eq_mul, hs]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (k : ℝ → X → X → ℝ)

/-- Quantitative Gaussian bounds and a local Euclidean volume lower bound
force uniform decay on any two positively separated sets. -/
theorem HasCoordinateHeatBounds.off_diagonal_small
    (hg : HasCoordinateHeatBounds μ k)
    (hnonneg : ∀ t, 0 < t → ∀ x y, 0 ≤ k t x y)
    (n : ℕ) (P S : Set X) {d D V : ℝ} (hd : 0 < d) (hD : 0 < D) (hV : 0 < V)
    (hsep : ∀ x ∈ P, ∀ y ∈ S, d ≤ dist x y)
    (hvol : ∀ y ∈ S, ∀ s, 0 < s → s ≤ D → V * s ^ n ≤ μ.real (ball y s))
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → ∀ x ∈ P, ∀ y ∈ S, |k t x y| ≤ η := by
  obtain ⟨C₁, C₂, hC₁, _hC₂, hbound⟩ := hg (1 / 2) (by norm_num) (by norm_num)
  have ha : 0 < d ^ 2 / (4 + 1 / 2 : ℝ) := div_pos (sq_pos_of_pos hd) (by norm_num)
  have hlim := (gaussianOffDiagonalEnvelope_tendsto ((n : ℝ) / 2) C₂ ha).const_mul (C₁ / V)
  obtain ⟨δ₀, hδ₀, hnear⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim η hη
  refine ⟨min δ₀ (D ^ 2), lt_min hδ₀ (sq_pos_of_pos hD), ?_⟩
  intro t ht htδ x hx y hy
  have htd : t < δ₀ := htδ.trans_le (min_le_left _ _)
  have htD : t < D ^ 2 := htδ.trans_le (min_le_right _ _)
  have hsqrt : Real.sqrt t ≤ D := by
    nlinarith [Real.sq_sqrt ht.le, Real.sqrt_nonneg t]
  have hv := hvol y hy (Real.sqrt t) (Real.sqrt_pos.2 ht) hsqrt
  rw [← sqrt_power_inverse n ht V] at hv
  have hu := gaussian_upper_of_inverse_power_volume μ k ht hd.le hC₁ hV
    (by norm_num : (0 : ℝ) < 4 + 1 / 2) x y (hbound t ht x y).2 hv (hsep x hx y hy)
  have hsmall : (C₁ / V) * gaussianOffDiagonalEnvelope ((n : ℝ) / 2)
      (d ^ 2 / (4 + 1 / 2)) C₂ t < η := by
    have h := hnear ht (by simpa only [Real.dist_eq, sub_zero, abs_of_pos ht] using htd)
    exact (le_abs_self _).trans_lt (by simpa only [Real.dist_eq, mul_zero, sub_zero] using h)
  rw [abs_of_nonneg (hnonneg t ht x y)]
  exact hu.trans hsmall.le

variable [BorelSpace X] [ProperSpace X] [μ.Regular]
  (hQ : QuadraticCheegerEnergy μ) (hk : IsContinuousHeatKernel μ hQ k)

include hk in
/-- The actual product-rule cutoff error tends to zero uniformly at
interior poles. Only local volume lower bounds on its annulus are used. -/
theorem GoodLaplacianCutoff.heat_error_uniformly_small
    (hg : HasCoordinateHeatBounds μ k) {p : X} {ρ C D V : ℝ}
    (χ : GoodLaplacianCutoff μ hQ p ρ C) (hρ : 0 < ρ) (hD : 0 < D) (hV : 0 < V)
    (n : ℕ) (hvol : ∀ y, ρ ≤ dist p y → dist p y ≤ 2 * ρ →
      ∀ s, 0 < s → s ≤ D → V * s ^ n ≤ μ.real (ball y s))
    (g : SobolevSpace μ hQ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → ∀ x ∈ ball p (ρ / 2),
      |∫ z, k t x z * cutoffSourceDensity μ hQ g χ.sobolev χ.laplacian z ∂μ| < ε := by
  let F := cutoffSourceDensity μ hQ g χ.sobolev χ.laplacian
  let A := ∫ z, |F z| ∂μ
  have hA : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
  have hden : 0 < A + 1 := by linarith
  let η := ε / (A + 1)
  have hη : 0 < η := div_pos hε hden
  obtain ⟨δ, hδ, hsmall⟩ := hg.off_diagonal_small μ k hk.nonneg n
    (ball p (ρ / 2)) {z | ρ ≤ dist p z ∧ dist p z ≤ 2 * ρ}
    (half_pos hρ) hD hV (by
      intro x hx y hy
      have hpx : dist p x < ρ / 2 := by simpa only [mem_ball, dist_comm] using hx
      have htri := dist_triangle p x y
      change ρ ≤ dist p y ∧ dist p y ≤ 2 * ρ at hy
      linarith [hy.1]) (by
      intro y hy s hs hsD
      exact hvol y hy.1 hy.2 s hs hsD) hη
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ x hx
  have hb := χ.heat_error_le μ hQ g (k t x) hη.le
    (fun z hz hz' => hsmall t ht htδ x hx z ⟨hz, hz'⟩)
  apply hb.trans_lt
  change η * A < ε
  dsimp only [η]
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hden).2
  nlinarith

end RegularPointCoordinates

end

end OAI
