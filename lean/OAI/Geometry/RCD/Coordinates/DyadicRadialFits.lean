import OAI.Geometry.RCD.Coordinates.RadialFitRecurrence
import OAI.Geometry.RCD.Metric.PositiveDistanceLocality

namespace OAI

/-! # Actual radial targets at successive dyadic source scales -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

/-- The fixed testing fraction commutes with every dyadic scale shift. -/
theorem distanceSourceRadius_testing_shift (r0 : ℝ) (i m : ℕ) :
    distanceSourceRadius r0 (i + m) / 64 =
      (1 / 2 : ℝ) ^ m * (distanceSourceRadius r0 i / 64) := by
  rw [distanceSourceRadius_add]
  simp only [one_div, inv_pow]
  ring

theorem distanceSourceRadius_antitone {r0 : ℝ} (hr0 : 0 ≤ r0) :
    Antitone (distanceSourceRadius r0) := by
  intro i j hij
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [distanceSourceRadius_add]
  exact div_le_self (by unfold distanceSourceRadius; positivity) (one_le_pow₀ (by norm_num))

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

namespace DyadicDistanceReplacements

/-- The canonical compact squared-distance datum at this source scale. -/
def distanceDatum {n : ℕ} {κ r0 B J C : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ) : SobolevSpace μ hQ :=
  positiveSquaredDistance μ hQ
    (by have := distanceSourceRadius_pos S.radius_pos i; positivity : 0 ≤ 4 * distanceSourceRadius r0 i)
    (T.cutoff i)

/-- On a later testing ball every earlier datum gives the same radial
pairing. This identifies the actual targets in the lagged recurrence. -/
theorem distanceDatum_pairing_later {n : ℕ} {κ r0 B J C : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) {i j : ℕ} (hij : i ≤ j)
    (a : SobolevSpace μ hQ) :
    localGamma μ hQ (T.distanceDatum μ hQ i) a =ᵐ[μ.restrict (ball p (distanceSourceRadius r0 j / 64))]
      localGamma μ hQ (T.distanceDatum μ hQ j) a := by
  have hi := (distanceSourceRadius_pos S.radius_pos i).le
  have hj := (distanceSourceRadius_pos S.radius_pos j).le
  have hmono := distanceSourceRadius_antitone S.radius_pos.le hij
  exact positiveSquaredDistance_pairing_independent μ hQ
    (by positivity) (by positivity) (by linarith) (by linarith) (T.cutoff i) (T.cutoff j) a

/-- Changing to the next canonical source datum preserves the actual
least-squares fit on its testing ball. -/
theorem distanceDatum_fit_later {n k : ℕ} {κ r0 B J C : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) {i j : ℕ} (hij : i ≤ j)
    (u : Fin k → SobolevSpace μ hQ) (a : SobolevSpace μ hQ)
    (hfin : μ (ball p (distanceSourceRadius r0 j / 64)) ≠ ∞) {A A' : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict (ball p (distanceSourceRadius r0 j / 64)), localGamma μ hQ a a x ≤ A)
    (ha' : ∀ᵐ x ∂μ.restrict (ball p (distanceSourceRadius r0 j / 64)), localGamma μ hQ a a x ≤ A') :
    radialFitError μ hQ u p (distanceSourceRadius r0 j / 64) hfin (T.distanceDatum μ hQ i) a ha =
      radialFitError μ hQ u p (distanceSourceRadius r0 j / 64) hfin (T.distanceDatum μ hQ j) a ha' :=
  radialFitError_congr μ hQ u p _ hfin _ a _ a ha ha'
    (T.distanceDatum_pairing_later μ hQ hij a)

end DyadicDistanceReplacements
end RegularPointCoordinates

end

end OAI
