import OAI.NumberTheory.CubicMoment.Estimates.MellinConjugation
import OAI.NumberTheory.CubicMoment.Estimates.HeightMassPartition

namespace OAI

/-! Exact changes of variable for the two signs of the Poisson rows.
The Jacobian 2π is retained. -/
noncomputable section
open scoped ContDiff
open MeasureTheory Filter
namespace CubicFirstMoment

lemma integral_scaled_mass (f g : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ, f t*g (c*t)) = c⁻¹*(∫ t : ℝ, f (t/c)*g t) := by
  have he := Measure.integral_comp_mul_left (fun t : ℝ => f (t/c)*g t) c
  simp only [abs_inv,abs_of_pos hc,smul_eq_mul,mul_div_cancel_left₀ _ hc.ne'] at he
  exact he

lemma integral_scaled_signed_mass (f g : ℝ → ℝ) {c : ℝ} (hc : 0 < c)
    (hplus : Integrable (fun t : ℝ => f t*g (c*t)))
    (hminus : Integrable (fun t : ℝ => f t*g (-(c*t)))) :
    (∫ t : ℝ, f t*((g (c*t)+g (-(c*t)))/2)) =
      ((∫ t : ℝ, f (t/c)*g t)+(∫ t : ℝ, f (-(t/c))*g t))/(2*c) := by
  have hminus' : (∫ t : ℝ, f t*g (-(c*t))) =
      c⁻¹*(∫ t : ℝ, f (-(t/c))*g t) := by
    have hn := integral_neg_eq_self (fun t : ℝ => f t*g (-(c*t)))
    simp only [mul_neg,neg_neg] at hn
    rw [← hn]
    exact integral_scaled_mass (fun t => f (-t)) g hc
  have hs (t : ℝ) : f t*((g (c*t)+g (-(c*t)))/2) =
      (f t*g (c*t))/2+(f t*g (-(c*t)))/2 := by ring
  simp_rw [hs]
  rw [integral_add (hplus.div_const 2) (hminus.div_const 2),
    integral_div,integral_div,integral_scaled_mass f g hc,hminus']
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma integrable_scaled_height_mass {f : ℝ → ℝ} (hf : Integrable f)
    (R : ℝ) (H : Finset Eisenstein) (v e : Eisenstein) (ℓ : ℤ) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (c : ℝ) :
    Integrable (fun t : ℝ => f t*fullStructuredHeightMass R H v e ℓ u W X (c*t)) := by
  obtain ⟨B,_hB,hB⟩ := fullStructuredHeightMass_bounded R H v e ℓ u W X
  apply hf.mul_bdd (c := B)
    ((continuous_fullStructuredHeightMass R H v e ℓ u W X).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable
  exact Eventually.of_forall (fun t => by
    change ‖fullStructuredHeightMass R H v e ℓ u W X (c*t)‖ ≤ B
    rw [Real.norm_eq_abs,abs_of_nonneg (fullStructuredHeightMass_nonneg R H v e ℓ u W X _)]
    exact hB (c*t))

lemma normMellin_signed_height_integral (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    (R : ℝ) (H : Finset Eisenstein) (v e : Eisenstein) (ℓ : ℤ) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (ρ : ℝ) :
    (∫ t : ℝ, ‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖*
      ((fullStructuredHeightMass R H v e ℓ u W X (2*Real.pi*t)+
        fullStructuredHeightMass R H v e ℓ u W X (-(2*Real.pi*t)))/2)) =
    ((∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖*
        fullStructuredHeightMass R H v e ℓ u W X t)+
      (∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ (-t)‖*
        fullStructuredHeightMass R H v e ℓ u W X t))/(4*Real.pi) := by
  have hf := (normDenominatorMellinCoefficient_integrable M hM V hV hV' ρ).norm
  have hp := integrable_scaled_height_mass hf R H v e ℓ u W X (2*Real.pi)
  have hn := integrable_scaled_height_mass hf R H v e ℓ u W X (-(2*Real.pi))
  simp only [neg_mul] at hn
  have he := integral_scaled_signed_mass
    (fun t => ‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖)
    (fullStructuredHeightMass R H v e ℓ u W X) (by positivity : 0 < 2*Real.pi) hp hn
  simpa only [arithmeticMellinCoefficient,neg_div,show (2:ℝ)*(2*Real.pi) = 4*Real.pi by ring] using he

end CubicFirstMoment

end

end OAI
