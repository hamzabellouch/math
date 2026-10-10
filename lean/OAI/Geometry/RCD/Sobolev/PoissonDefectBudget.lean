import OAI.Geometry.RCD.Metric.DistanceSourceBudget

namespace OAI

/-! # The summable defect including the Poisson curvature remainder -/

open Set Metric MeasureTheory
open scoped BigOperators

noncomputable section
namespace RegularPointCoordinates

theorem distanceSourceRadius_sq (r0 : ℝ) (i : ℕ) :
    (distanceSourceRadius r0 i) ^ 2 = r0 ^ 2 / 4 * (1 / 4 : ℝ) ^ i := by
  have h := distanceSourceRadius_four_sq r0 i
  nlinarith

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- The second term is the actual curvature remainder in the shifted
Poisson mass estimate, in the same normalized units as the full source. -/
def normalizedPoissonDefect {n : ℕ} {κ r0 : ℝ} {p : X}
    (S : DyadicDistanceSources μ hQ n κ p r0) (i : ℕ) : ℝ :=
  normalizedDistanceSourceMass μ hQ S i + κ * (distanceSourceRadius r0 i) ^ 2 *
    ((distanceSourceRadius r0 i) ^ (-(n : ℝ)) * μ.real (ball p (distanceSourceRadius r0 i)))

theorem normalizedPoissonDefect_nonneg {n : ℕ} {κ r0 : ℝ} {p : X}
    (S : DyadicDistanceSources μ hQ n κ p r0) (hκ : 0 ≤ κ) (i : ℕ) :
    0 ≤ normalizedPoissonDefect μ hQ S i := by
  have hs := distanceSourceRadius_pos S.radius_pos i
  dsimp only [normalizedPoissonDefect, normalizedDistanceSourceMass]
  positivity

/-- Source and curvature masses have exactly the same normalization;
the identity uses the actual volume, not a Euclidean replacement. -/
theorem normalizedPoissonDefect_units {n : ℕ} {κ r0 : ℝ} {p : X}
    (S : DyadicDistanceSources μ hQ n κ p r0) (i : ℕ) :
    (distanceSourceRadius r0 i) ^ (n : ℝ) * normalizedPoissonDefect μ hQ S i =
      (S.source i).real (ball p (distanceSourceRadius r0 i)) +
        κ * (distanceSourceRadius r0 i) ^ 2 * μ.real (ball p (distanceSourceRadius r0 i)) := by
  have hs := distanceSourceRadius_pos S.radius_pos i
  have hp := Real.rpow_pos_of_pos hs (n : ℝ)
  dsimp only [normalizedPoissonDefect, normalizedDistanceSourceMass]
  rw [Real.rpow_neg hs.le]
  field_simp [hp.ne']

/-- The extra curvature remainder costs at most kappa*C*r0²/3 in the
total budget. The original positive source measures remain unchanged. -/
theorem DyadicDistanceSources.poisson_defect_budget {n : ℕ} {κ r0 C : ℝ} {p : X}
    (S : DyadicDistanceSources μ hQ n κ p r0) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hsource : Summable (normalizedDistanceSourceMass μ hQ S))
    (hvolume : ∀ i, (distanceSourceRadius r0 i) ^ (-(n : ℝ)) *
      μ.real (ball p (distanceSourceRadius r0 i)) ≤ C) :
    Summable (normalizedPoissonDefect μ hQ S) ∧
      (∑' i, normalizedPoissonDefect μ hQ S i) ≤
        (∑' i, normalizedDistanceSourceMass μ hQ S i) + κ * C * r0 ^ 2 / 3 := by
  let V := fun i => κ * (distanceSourceRadius r0 i) ^ 2 *
    ((distanceSourceRadius r0 i) ^ (-(n : ℝ)) * μ.real (ball p (distanceSourceRadius r0 i)))
  have hV (i : ℕ) : 0 ≤ V i := by
    have hs := distanceSourceRadius_pos S.radius_pos i
    dsimp only [V]
    positivity
  have hpoint (i : ℕ) : V i ≤ (κ * C * r0 ^ 2 / 4) * (1 / 4 : ℝ) ^ i := by
    calc
      _ ≤ κ * (distanceSourceRadius r0 i) ^ 2 * C :=
        mul_le_mul_of_nonneg_left (hvolume i) (by positivity)
      _ = _ := by rw [distanceSourceRadius_sq]; ring
  have hfinite (k : ℕ) : (∑ i ∈ Finset.range k, V i) ≤ κ * C * r0 ^ 2 / 3 := by
    have hh := Finset.sum_le_sum (s := Finset.range k) (fun i _ => hpoint i)
    rw [← Finset.mul_sum] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (sum_range_quarter_pow_le k)
      (by positivity : 0 ≤ κ * C * r0 ^ 2 / 4)).trans_eq (by ring))
  have hVs : Summable V := summable_of_sum_range_le hV hfinite
  refine ⟨hsource.add hVs, ?_⟩
  change (∑' (i : ℕ), (normalizedDistanceSourceMass μ hQ S i + V i)) ≤ _
  rw [hsource.tsum_add hVs]
  exact add_le_add (le_refl _) (Real.tsum_le_of_sum_range_le hV hfinite)

end RegularPointCoordinates

end

end OAI
