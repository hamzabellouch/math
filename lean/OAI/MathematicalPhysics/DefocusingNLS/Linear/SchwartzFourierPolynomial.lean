import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadianFourierSeries

namespace OAI

/-! # Finite physical cutoffs are Schwartz

This supplies the dense-domain objects used when extending localization into
the manuscript's completed homogeneous Sobolev space.
-/

open scoped SchwartzMap RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem spatialFourierCharacter_temperate (n : frequencyLattice) :
    (spatialFourierCharacter n).HasTemperateGrowth := by
  have h := Complex.hasTemperateGrowth_exp_mul_I.comp
    (((innerSL ℝ).flip (n : E)).hasTemperateGrowth)
  exact h

noncomputable def modulatedSchwartzCutoff (χ : 𝓢(E, ℂ)) (n : frequencyLattice) : 𝓢(E, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (spatialFourierCharacter n) χ

@[simp] theorem modulatedSchwartzCutoff_apply (χ : 𝓢(E, ℂ)) (n : frequencyLattice) (y : E) :
    modulatedSchwartzCutoff χ n y = spatialFourierCharacter n y * χ y := by
  exact SchwartzMap.smulLeftCLM_apply_apply (spatialFourierCharacter_temperate n) χ y

/-- The actual finite cutoff polynomial, bundled in the Schwartz space. -/
noncomputable def localizedSchwartzPolynomial (L : ℝ) (hL : 0 < L) (χ : 𝓢(E, ℂ))
    (S : Finset frequencyLattice) (v : frequencyLattice → ℂ) : 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((Units.mk0 L⁻¹ (inv_ne_zero hL.ne')) • ContinuousLinearEquiv.refl ℝ E)
    (∑ n ∈ S, v n • modulatedSchwartzCutoff χ n)

@[simp] theorem localizedSchwartzPolynomial_apply (L : ℝ) (hL : 0 < L)
    (χ : 𝓢(E, ℂ)) (S : Finset frequencyLattice) (v : frequencyLattice → ℂ) (y : E) :
    localizedSchwartzPolynomial L hL χ S v y = localizedFourierPolynomial L χ S v y := by
  change (∑ n ∈ S, v n • modulatedSchwartzCutoff χ n) (L⁻¹ • y) = _
  simp only [sum_apply, smul_apply, modulatedSchwartzCutoff_apply,
    smul_eq_mul, localizedFourierPolynomial, spatialFourierCharacter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

end DefocusingNLS

end OAI
