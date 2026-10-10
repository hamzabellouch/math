import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.HeightTemperedDistribution
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalFourierMultiplier
import OAI.Analysis.RieszRectifiability.Kernel.SchwartzNormDivision

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Filter
open scoped FourierTransform

theorem fractionalSchwartz_norm_division_identity (p : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : 𝓢(Ambient (p + 1), ℂ),
      ∀ hc : HasCompactSupport g, ∀ hz : (0 : Ambient (p + 1)) ∉ tsupport g,
      ∀ x : Ambient (p + 1),
      fractionalSchwartzTest p (𝓕⁻ (schwartzNormDivision g hc hz)) x = c • (𝓕⁻ g) x := by
  obtain ⟨c, hc, hm⟩ := fractionalSchwartz_positive_norm_multiplier p
  refine ⟨c, hc, fun g hgc hgz x => ?_⟩
  rw [hm, schwartz_inverse_fourier_phase_integral]
  erw [← integral_smul c]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ξ
  dsimp only
  calc
    _ = c • (‖ξ‖ • (fourierPhase ξ x * schwartzNormDivision g hgc hgz ξ)) :=
      mul_smul c ‖ξ‖ (fourierPhase ξ x * schwartzNormDivision g hgc hgz ξ)
    _ = c • (fourierPhase ξ x * (‖ξ‖ • schwartzNormDivision g hgc hgz ξ)) :=
      congrArg (fun z : ℂ => c • z)
        (Algebra.mul_smul_comm ‖ξ‖ (fourierPhase ξ x) (schwartzNormDivision g hgc hgz ξ)).symm
    _ = _ := by
      rw [schwartzNormDivision_norm_mul]

theorem height_inverse_fourier_zero_of_fractional_equation (p : ℕ)
    (w : Ambient (p + 1) → ℝ)
    (heq : ∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
      (∫ x, w x • fractionalSchwartzTest p g x) = 0)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hc : HasCompactSupport g)
    (hz : (0 : Ambient (p + 1)) ∉ tsupport g) :
    (∫ x, w x • (𝓕⁻ g) x) = 0 := by
  obtain ⟨c, hcp, hm⟩ := fractionalSchwartz_norm_division_identity p
  have h := heq (𝓕⁻ (schwartzNormDivision g hc hz))
    (schwartzNormDivision_inverse_mean_zero g hc hz)
  have hscalar : c • (∫ x, w x • (𝓕⁻ g) x) = (0 : ℂ) := by
    calc
      _ = ∫ x, c • (w x • (𝓕⁻ g) x) := (integral_smul c _).symm
      _ = ∫ x, w x • fractionalSchwartzTest p (𝓕⁻ (schwartzNormDivision g hc hz)) x := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        dsimp only
        rw [hm g hc hz x]
        exact smul_comm c (w x) ((𝓕⁻ g) x)
      _ = 0 := h
  exact (smul_eq_zero.mp hscalar).resolve_left hcp.ne'

theorem height_distribution_inverse_fourier_annihilates_away_zero (p : ℕ)
    (w : Ambient (p + 1) → ℝ) (hw : Measurable w) (q : ℕ)
    (hweight : Integrable (fun x => |w x| * polynomialDecay q x) volume)
    (heq : ∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
      (∫ x, w x • fractionalSchwartzTest p g x) = 0)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hc : HasCompactSupport g)
    (hz : (0 : Ambient (p + 1)) ∉ tsupport g) :
    (𝓕⁻ (heightTemperedDistribution volume w hw q hweight) : 𝓢'(Ambient (p + 1), ℂ)) g = 0 := by
  rw [TemperedDistribution.fourierInv_apply, heightTemperedDistribution_apply]
  exact height_inverse_fourier_zero_of_fractional_equation p w heq g hc hz

theorem represented_height_inverse_fourier_annihilates_away_zero (p : ℕ)
    (w : Ambient (p + 1) → ℝ) (T : 𝓢'(Ambient (p + 1), ℂ))
    (hT : ∀ g : 𝓢(Ambient (p + 1), ℂ), T g = ∫ x, w x • g x)
    (heq : ∀ g : 𝓢(Ambient (p + 1), ℂ), (∫ x, g x) = 0 →
      (∫ x, w x • fractionalSchwartzTest p g x) = 0)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hc : HasCompactSupport g)
    (hz : (0 : Ambient (p + 1)) ∉ tsupport g) :
    (𝓕⁻ T : 𝓢'(Ambient (p + 1), ℂ)) g = 0 := by
  rw [TemperedDistribution.fourierInv_apply, hT]
  exact height_inverse_fourier_zero_of_fractional_equation p w heq g hc hz

end

end RieszRectifiability

end OAI
