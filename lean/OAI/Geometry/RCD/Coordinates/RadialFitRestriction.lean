import OAI.Geometry.RCD.Harmonic.NearbyMeanGrams
import OAI.Geometry.RCD.Coordinates.NormalizedLocalL2

namespace OAI

/-! # Restricting the value and energy bounds of an actual radial fit -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
/-- A normalized squared value error only pays the actual volume ratio
when the common commutator ball is smaller than the radial fitting ball. -/
theorem normalized_fit_restrict_sq {s t : Set X} (hts : t ⊆ s)
    (hs : μ s ≠ ∞) (ht : μ t ≠ ∞) (hs0 : 0 < μ.real s) (ht0 : 0 < μ.real t)
    (f : SobolevSpace μ hQ) {C E : ℝ} (hE : 0 ≤ E)
    (hvol : μ.real s ≤ C * μ.real t)
    (hfit : ‖normalizeLocalL2 μ s hs (SobolevSpace.restrictLp μ hQ s f)‖ ^ 2 ≤ E) :
    ‖normalizeLocalL2 μ t ht (SobolevSpace.restrictLp μ hQ t f)‖ ^ 2 ≤ C * E := by
  rw [normalized_sobolev_mean_sq] at hfit ⊢
  apply average_nonneg_le_of_subset μ hts ht0 hs0
    (Lp.memLp (SobolevSpace.toLp μ hQ f)).integrable_sq.integrableOn (fun x => sq_nonneg _) hE hvol hfit

omit [ProperSpace X] in
/-- The identical volume-ratio loss applies to the squared gradient error. -/
theorem normalized_fit_energy_restrict {s t : Set X} (hts : t ⊆ s)
    (hs0 : 0 < μ.real s) (ht0 : 0 < μ.real t)
    (f : SobolevSpace μ hQ) {C E : ℝ} (hE : 0 ≤ E)
    (hvol : μ.real s ≤ C * μ.real t)
    (hfit : (μ.real s)⁻¹ * (∫ x in s, localGamma μ hQ f f x ∂μ) ≤ E) :
    (μ.real t)⁻¹ * (∫ x in t, localGamma μ hQ f f x ∂μ) ≤ C * E := by
  have hself := localGamma_self μ hQ f
  rw [integral_congr_ae (ae_restrict_of_ae hself)] at hfit ⊢
  apply average_nonneg_le_of_subset μ hts ht0 hs0
    (Lp.memLp (SobolevSpace.minimalSlope μ hQ f)).integrable_sq.integrableOn
    (fun x => sq_nonneg _) hE hvol hfit

end RegularPointCoordinates

end

end OAI
