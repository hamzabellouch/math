import OAI.Geometry.RCD.Harmonic.RadialQuadraticLimit
import OAI.Geometry.RCD.Harmonic.QuadraticModelValues

namespace OAI

/-! # The quadratic radial limit from mean-square Poisson error -/

open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
/-- Metric approximation controls the dimensionless distance quadratic
against the actual bounded coordinate quadratic. -/
theorem coordinateQuadratic_dimensionless_error {n : ℕ} {p : X} {r S ε : ℝ}
    (hr : 0 < r) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (u : Fin n → SobolevSpace μ hQ) (C : ℝ≥0) (V : X → Euclidean n)
    (hu : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C)
    (hrep : ∀ j, SobolevSpace.toLp μ hQ (u j) =ᵐ[μ.restrict (ball p (S * r))] fun x => V x j)
    (hmetric : IsPointedApproximation p 0 r S ε V) (hcenter : V p = 0)
    (q : SobolevSpace μ hQ)
    (hq : SobolevSpace.toLp μ hQ q =ᵐ[μ.restrict (ball p (S * r))]
      fun x => dist p x ^ 2 / (2 * r ^ 2)) :
    ∀ᵐ x ∂μ.restrict (ball p (S * r)),
      |SobolevSpace.toLp μ hQ (q - coordinateQuadratic μ hQ u C) x| ≤
        ε * (2 * S + ε) / 2 := by
  filter_upwards [hq, coordinateQuadratic_eq_norm μ hQ u C V hu hrep,
    ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ hQ q)
      (SobolevSpace.toLp μ hQ (coordinateQuadratic μ hQ u C))),
    ae_restrict_mem measurableSet_ball] with x hqx hHx hsub hx
  rw [map_sub, hsub, Pi.sub_apply, hHx]
  have hzero : |r ^ 2 * SobolevSpace.toLp μ hQ q x - dist p x ^ 2 / 2| ≤ r ^ 2 * 0 := by
    rw [hqx]
    have heq : r ^ 2 * (dist p x ^ 2 / (2 * r ^ 2)) - dist p x ^ 2 / 2 = 0 := by
      field_simp
      ring
    rw [heq, abs_zero, mul_zero]
  simpa only [zero_add] using radial_quadratic_value_error hr hS hε hmetric hcenter hx.le hzero

omit [ProperSpace X] in
/-- The normalized coordinate error is bounded by the Poisson L2 error
plus the metric approximation error. No uniform vanishing height is needed. -/
theorem radial_quadratic_l2_bound {n : ℕ} {p : X} {r S ε : ℝ}
    (hr : 0 < r) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hfin : μ (ball p (S * r)) ≠ ∞)
    (u : Fin n → SobolevSpace μ hQ) (C : ℝ≥0) (V : X → Euclidean n)
    (hu : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C)
    (hrep : ∀ j, SobolevSpace.toLp μ hQ (u j) =ᵐ[μ.restrict (ball p (S * r))] fun x => V x j)
    (hmetric : IsPointedApproximation p 0 r S ε V) (hcenter : V p = 0)
    (f q : SobolevSpace μ hQ)
    (hq : SobolevSpace.toLp μ hQ q =ᵐ[μ.restrict (ball p (S * r))]
      fun x => dist p x ^ 2 / (2 * r ^ 2)) :
    ‖normalizeLocalL2 μ (ball p (S * r)) hfin (SobolevSpace.restrictLp μ hQ
      (ball p (S * r)) (f - coordinateQuadratic μ hQ u C))‖ ≤
    ‖normalizeLocalL2 μ (ball p (S * r)) hfin (SobolevSpace.restrictLp μ hQ
      (ball p (S * r)) (f - q))‖ + ε * (2 * S + ε) / 2 := by
  have hb : ‖normalizeLocalL2 μ (ball p (S * r)) hfin (SobolevSpace.restrictLp μ hQ
      (ball p (S * r)) (q - coordinateQuadratic μ hQ u C))‖ ≤ ε * (2 * S + ε) / 2 := by
    apply normalized_norm_le_of_bound μ _ hfin _ (by positivity)
    filter_upwards [coordinateQuadratic_dimensionless_error μ hQ hr hS hε u C V hu hrep hmetric hcenter q hq,
      SobolevSpace.restrictLp_coe μ hQ (ball p (S * r)) (q - coordinateQuadratic μ hQ u C)] with x hx heq
    rwa [heq]
  have heq : f - coordinateQuadratic μ hQ u C = (f - q) + (q - coordinateQuadratic μ hQ u C) := by abel
  rw [heq, map_add]
  simp only [normalizeLocalL2, smul_add] at hb ⊢
  exact (norm_add_le _ _).trans (add_le_add le_rfl hb)

omit [ProperSpace X] in
/-- Strong mean-square convergence to squared distance and metric
approximation give the radial value limit in the Euclidean coordinates. -/
theorem radial_quadratic_l2_limit {n : ℕ} {S : ℝ} (hS : 0 ≤ S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (u : ℕ → Fin n → SobolevSpace μ hQ)
    (C : ℕ → ℝ≥0) (V : ℕ → X → Euclidean n) (f q : ℕ → SobolevSpace μ hQ)
    (hr : ∀ i, 0 < r i) (hε : ∀ i, 0 ≤ ε i) (hε0 : Tendsto ε atTop (𝓝 0))
    (hfin : ∀ i, μ (ball (p i) (S * r i)) ≠ ∞)
    (hu : ∀ i j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u i j) x| ≤ C i)
    (hrep : ∀ i j, SobolevSpace.toLp μ hQ (u i j) =ᵐ[μ.restrict (ball (p i) (S * r i))]
      fun x => V i x j)
    (hmetric : ∀ i, IsPointedApproximation (p i) 0 (r i) S (ε i) (V i))
    (hcenter : ∀ i, V i (p i) = 0)
    (hq : ∀ i, SobolevSpace.toLp μ hQ (q i) =ᵐ[μ.restrict (ball (p i) (S * r i))]
      fun x => dist (p i) x ^ 2 / (2 * r i ^ 2))
    (herror : Tendsto (fun i => ‖normalizeLocalL2 μ (ball (p i) (S * r i)) (hfin i)
      (SobolevSpace.restrictLp μ hQ (ball (p i) (S * r i)) (f i - q i))‖) atTop (𝓝 0)) :
    Tendsto (fun i => (μ.real (ball (p i) (S * r i)))⁻¹ *
      ∫ x in ball (p i) (S * r i), (SobolevSpace.toLp μ hQ (f i) x - ‖V i x‖ ^ 2 / 2) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  let H i := coordinateQuadratic μ hQ (u i) (C i)
  have hlim : Tendsto (fun i => ‖normalizeLocalL2 μ (ball (p i) (S * r i)) (hfin i)
      (SobolevSpace.restrictLp μ hQ (ball (p i) (S * r i)) (f i - H i))‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun i => radial_quadratic_l2_bound μ hQ (hr i) hS (hε i) (hfin i)
        (u i) (C i) (V i) (hu i) (hrep i) (hmetric i) (hcenter i) (f i) (q i) (hq i))
    have hb := herror.add ((hε0.mul ((tendsto_const_nhds (x := 2 * S)).add hε0)).div_const 2)
    simpa using hb
  have heq (i : ℕ) : ‖normalizeLocalL2 μ (ball (p i) (S * r i)) (hfin i)
      (SobolevSpace.restrictLp μ hQ (ball (p i) (S * r i)) (f i - H i))‖ ^ 2 =
      (μ.real (ball (p i) (S * r i)))⁻¹ *
        ∫ x in ball (p i) (S * r i), (SobolevSpace.toLp μ hQ (f i) x - ‖V i x‖ ^ 2 / 2) ^ 2 ∂μ := by
    rw [normalized_sobolev_mean_sq]
    congr 1
    apply integral_congr_ae
    filter_upwards [coordinateQuadratic_eq_norm μ hQ (u i) (C i) (V i) (hu i) (hrep i),
      ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ hQ (f i))
        (SobolevSpace.toLp μ hQ (H i)))] with x hx hs
    rw [map_sub, hs, Pi.sub_apply, hx]
  simpa only [heq, zero_pow (by decide : 2 ≠ 0)] using hlim.pow 2

end RegularPointCoordinates

end

end OAI
