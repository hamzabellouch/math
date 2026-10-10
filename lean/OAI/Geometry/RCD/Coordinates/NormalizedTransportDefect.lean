import OAI.Geometry.RCD.Transport.ActualRadialTransportDefect
import OAI.Geometry.RCD.Sobolev.PoissonDefectBudget
import OAI.Geometry.RCD.Harmonic.RadialVolumeUnits
import OAI.Geometry.RCD.Metric.VolumeRigidityInput

namespace OAI

/-! # The actual transport error in the normalized source units -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- At the fixed projection radius, the full Poisson defect supplies
exactly the radial error budget required by normalized transport. -/
theorem DyadicDistanceReplacements.normalized_transport_defect
    {n : ℕ} {κ r0 B J C σ : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ)
    (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    (hbudget : normalizedPoissonDefect μ hQ S i ≤ σ ^ 2)
    (hvol : |μ.real (ball p (distanceSourceRadius r0 i / 2048)) /
      (euclideanUnitVolume n * (distanceSourceRadius r0 i / 2048) ^ n) - 1| ≤ 1 / 4) :
    let R := distanceSourceRadius r0 i / 2048
    ∃ g : X → ℝ, MemLp g 2 μ ∧
      (localGamma μ hQ (T.replacement i) (inwardSobolev μ hQ p (3 * R)) =ᵐ[
        μ.restrict (ball p (3 * R))] fun x => g x - dist p x) ∧
      (∫ x in ball p (4 * R), (g x) ^ 2 ∂μ) ≤
        (B * (2048 : ℝ) ^ 2 * ((4 / (3 * euclideanUnitVolume n)) * (2048 : ℝ) ^ n)) *
          R ^ 2 * μ.real (ball p R) * σ ^ 2 := by
  dsimp only
  let s := distanceSourceRadius r0 i
  let R := s / 2048
  let V := μ.real (ball p R)
  let W := (4 / (3 * euclideanUnitVolume n)) * (2048 : ℝ) ^ n
  have hs : 0 < s := distanceSourceRadius_pos S.radius_pos i
  have hR : 0 < R := by dsimp only [R]; positivity
  obtain ⟨hV, hlo, _⟩ := quarter_volume_bounds hR (euclideanUnitVolume_pos n) hvol
  have hunit : W * ((3 / 4 : ℝ) * euclideanUnitVolume n * R ^ n) = s ^ (n : ℝ) := by
    dsimp only [W, R]
    rw [Real.rpow_natCast, div_pow]
    field_simp [(euclideanUnitVolume_pos n).ne']
  have hratio : s ^ (n : ℝ) ≤ W * V := by
    rw [← hunit]
    exact mul_le_mul_of_nonneg_left hlo (by
      have homega := euclideanUnitVolume_pos n
      dsimp only [W]
      positivity)
  have hmass : (S.source i).real (ball p s) ≤ s ^ (n : ℝ) * σ ^ 2 := by
    have hsource : (S.source i).real (ball p s) ≤
        s ^ (n : ℝ) * normalizedPoissonDefect μ hQ S i := by
      rw [normalizedPoissonDefect_units]
      exact le_add_of_nonneg_right (by positivity)
    exact hsource.trans (mul_le_mul_of_nonneg_left hbudget (Real.rpow_nonneg hs.le _))
  obtain ⟨g, hg, hradial, he⟩ := T.radial_transport_defect μ hQ i hR
    (by dsimp only [R]; linarith : 3 * R ≤ 4 * s)
  refine ⟨g, hg, hradial, ?_⟩
  have hsize : (S.source i).real (ball p s) ≤ W * V * σ ^ 2 :=
    hmass.trans (mul_le_mul_of_nonneg_right hratio (sq_nonneg _))
  calc
    _ ≤ (W * V * σ ^ 2) * (B * s ^ 2) :=
      he.trans (mul_le_mul_of_nonneg_right hsize (mul_nonneg hB (sq_nonneg _)))
    _ = (B * (2048 : ℝ) ^ 2 * W) * R ^ 2 * V * σ ^ 2 := by dsimp only [R]; ring

end RegularPointCoordinates

end

end OAI
