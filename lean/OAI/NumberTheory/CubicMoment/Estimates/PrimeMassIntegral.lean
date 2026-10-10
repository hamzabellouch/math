import OAI.NumberTheory.CubicMoment.Estimates.PrimeCoprimeMass
import OAI.NumberTheory.CubicMoment.Estimates.MellinSignedIntegration

namespace OAI

/-! Integrating the exact common-divisor decomposition. The large-divisor
majorant may be uniform in height; the empty row retains its full Mellin integral. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fullPrime_coprime_mass_integral_le {R D : ℝ} (hD : 1 ≤ D)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hrough : ∀ i, D < X i) (e : Eisenstein) (H U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (u : ℝ) {N : ℝ} (hN : 0 < N)
    {f : ℝ → ℝ} (hf : Integrable f) (hf0 : ∀ t, 0 ≤ f t) {A : ℝ}
    (hlarge : ∀ t, (∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p)),
      fullPrimeDivisorMellinMass R W X e H u N (∏ p ∈ s, p) t) ≤ A) :
    (∫ t : ℝ, f t * coprimeMellinMass (fullSquarefreePrimeSupport R W X e) H U
      (fun a => star (fullPrimeCoefficient R W X a*mellinPhase u (norm a)))
      (fun a => star (fullPrimeCoefficient R W X a*mellinPhase u (norm a)))
      (fun a => norm a/N) t) ≤
    (∫ t : ℝ, f t*((fullStructuredHeightMass R H 1 e 0 u W X (2*Real.pi*t)+
      fullStructuredHeightMass R H 1 e 0 u W X (-(2*Real.pi*t)))/2)) + A*(∫ t : ℝ, f t) := by
  have hp := integrable_scaled_height_mass hf R H 1 e 0 u W X (2*Real.pi)
  have hn := integrable_scaled_height_mass hf R H 1 e 0 u W X (-(2*Real.pi))
  simp only [neg_mul] at hn
  have hs : Integrable (fun t : ℝ => f t*((fullStructuredHeightMass R H 1 e 0 u W X (2*Real.pi*t)+
      fullStructuredHeightMass R H 1 e 0 u W X (-(2*Real.pi*t)))/2)) := by
    convert (hp.add hn).div_const 2 using 1
    ext t
    dsimp only [Pi.add_apply]
    ring
  calc
    _ ≤ ∫ t : ℝ, f t*((fullStructuredHeightMass R H 1 e 0 u W X (2*Real.pi*t)+
        fullStructuredHeightMass R H 1 e 0 u W X (-(2*Real.pi*t)))/2)+A*f t := by
      apply integral_mono_of_nonneg
        (Eventually.of_forall (fun t => mul_nonneg (hf0 t) (coprimeMellinMass_nonneg _ _ _ _ _ _ t)))
        (hs.add (hf.const_mul A))
      filter_upwards with t
      rw [fullPrime_coprime_mass_split hD W X hX hlo hhi hrough e H U hU u t hN]
      calc
        _ ≤ f t*((fullStructuredHeightMass R H 1 e 0 u W X (2*Real.pi*t)+
            fullStructuredHeightMass R H 1 e 0 u W X (-(2*Real.pi*t)))/2+A) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl (hlarge t)) (hf0 t)
        _ = _ := by dsimp only [Pi.add_apply]; ring
    _ = _ := by rw [integral_add hs (hf.const_mul A),integral_const_mul]

end CubicFirstMoment

end

end OAI
