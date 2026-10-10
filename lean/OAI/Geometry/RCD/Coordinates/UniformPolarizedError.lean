import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Harmonic.OperatorQuadraticDerivative
import OAI.Geometry.RCD.Coordinates.RegularHeatCutoff
import Mathlib.Topology.Order.LeftRightNhds

namespace OAI

/-! # Uniform operator control from finitely many scalar cutoff errors -/

open Set Filter MeasureTheory
open scoped Topology NNReal

noncomputable section

namespace RegularPointCoordinates

/-- Finitely many coordinate tests turn uniform scalar decay into uniform
operator decay; the scalar threshold may initially depend on the direction. -/
theorem polarizedDerivative_uniformly_small {X : Type*} {n : ℕ}
    (d : ℝ → X → Euclidean n → ℝ) (P : Set X)
    (hd : ∀ v, ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ t, 0 < t → t < δ → ∀ x ∈ P, |d t x v| < η)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → ∀ x ∈ P,
      ‖polarizedDerivative (d t x)‖ < ε := by
  let C : ℝ := (n : ℝ) ^ 2 * (3 / 2)
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) (by norm_num)
  let η := ε / (C + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have he (v : Euclidean n) : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x ∈ P, |d t x v| ≤ η := by
    obtain ⟨δ, hδ, hb⟩ := hd v η hη
    apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
    exact ⟨δ, hδ, fun t ht x hx => (hb t ht.1 ht.2 x hx).le⟩
  have hs : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i : Fin n, ∀ x ∈ P,
      |d t x (EuclideanSpace.single i 1)| ≤ η :=
    Filter.eventually_all.mpr fun i => he (EuclideanSpace.single i 1)
  have hp : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i j : Fin n, ∀ x ∈ P,
      |d t x (EuclideanSpace.single i 1 + EuclideanSpace.single j 1)| ≤ η :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      he (EuclideanSpace.single i 1 + EuclideanSpace.single j 1)
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x ∈ P,
      ‖polarizedDerivative (d t x)‖ < ε := by
    filter_upwards [hs, hp] with t ht ht' x hx
    have hb := polarizedDerivative_norm_le (d t x) hη.le
      (fun i => ht i x hx) (fun i j => ht' i j x hx)
    apply hb.trans_lt
    change (n : ℝ) ^ 2 * (3 / 2 * η) < ε
    have hlt : C * η < ε := by
      dsimp only [η]
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ (by linarith : 0 < C + 1)).mpr
      nlinarith
    simpa only [C, mul_assoc] using hlt
  obtain ⟨δ, hδ, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  exact ⟨δ, hδ, fun t ht htδ => hb ⟨ht, htδ⟩⟩

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : MeasureTheory.Measure X) [μ.Regular]
  (hQ : QuadraticCheegerEnergy μ) {k : ℝ → X → X → ℝ}
  (hk : IsContinuousHeatKernel μ hQ k)

/-- The operator cutoff error is built from the actual scalar product-rule
sources. It is not an additional analytic input. -/
def harmonicHeatError {n : ℕ} {U : Euclidean n →L[ℝ] SobolevSpace μ hQ}
    {M : PositiveBilinearMeasure X (Euclidean n)} {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0}
    (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
    {ρ C : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ C) (t : ℝ) (x : X) :
    Euclidean n →L[ℝ] Euclidean n :=
  polarizedDerivative fun v => ∫ z, k t x z *
    cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z ∂μ

include hk in
/-- Local Euclidean volume bounds make the canonical error uniformly
small in operator norm throughout the inner pole ball. -/
theorem harmonicHeatError_uniformly_small (hg : HasCoordinateHeatBounds μ k)
    {n : ℕ} {U : Euclidean n →L[ℝ] SobolevSpace μ hQ}
    {M : PositiveBilinearMeasure X (Euclidean n)} {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0}
    (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
    {ρ C D V : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ C)
    (hρ : 0 < ρ) (hD : 0 < D) (hV : 0 < V)
    (hvol : ∀ y, ρ ≤ dist p y → dist p y ≤ 2 * ρ →
      ∀ s, 0 < s → s ≤ D → V * s ^ n ≤ μ.real (Metric.ball y s))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → ∀ x ∈ Metric.ball p (ρ / 2),
      ‖harmonicHeatError μ hQ (k := k) G χ t x‖ < ε := by
  apply polarizedDerivative_uniformly_small _ _ _ hε
  intro v η hη
  exact χ.heat_error_uniformly_small μ k hQ hk hg hρ hD hV n hvol (G v).energy hη

end RegularPointCoordinates

end

end OAI
