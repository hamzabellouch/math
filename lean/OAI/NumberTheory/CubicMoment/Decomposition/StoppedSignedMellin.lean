import OAI.NumberTheory.CubicMoment.Decomposition.StoppedMellinRows
import OAI.NumberTheory.CubicMoment.Estimates.MellinSignedIntegration

namespace OAI

/-! Exact signed arithmetic-height representation of the divisor mass.
All finite coefficient supports and coprimality rows are retained. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma divisor_normMellin_signed_integral
    (m : ℝ) (hm : 0 < m) (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hS : ∀ n ∈ S, primary n) (u ρ : ℝ) {N : ℝ} (hN : 0 < N) :
    (∫ t : ℝ, ‖normDenominatorMellinCoefficient m hm Φ hΦ hΦ' ρ t‖*
      twistedCoprimeMellinMass S H U β (fun a => norm a/N) u t) =
    ((∫ t : ℝ, ‖arithmeticMellinCoefficient m hm Φ hΦ hΦ' ρ t‖*
        divisorCharacterMass S H U β (t+u))+
      (∫ t : ℝ, ‖arithmeticMellinCoefficient m hm Φ hΦ hΦ' ρ (-t)‖*
        divisorCharacterMass S H U β (t+u)))/(4*Real.pi) := by
  let G := fun t => divisorCharacterMass S H U β (t+u)
  let f := fun t => ‖normDenominatorMellinCoefficient m hm Φ hΦ hΦ' ρ t‖
  have hG : Continuous G :=
    (divisorCharacterMass_continuous S H U β).comp (continuous_id.add continuous_const)
  have hf : Integrable f := (normDenominatorMellinCoefficient_integrable m hm Φ hΦ hΦ' ρ).norm
  have hp : Integrable (fun t => f t*G (2*Real.pi*t)) :=
    hf.mul_bdd (hG.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => divisorCharacterMass_bound S H U β hS _))
  have hn : Integrable (fun t => f t*G (-(2*Real.pi*t))) :=
    hf.mul_bdd (hG.comp (continuous_neg.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => divisorCharacterMass_bound S H U β hS _))
  have he := integral_scaled_signed_mass f G (by positivity : 0 < 2*Real.pi) hp hn
  have hpoint (t : ℝ) : twistedCoprimeMellinMass S H U β (fun a => norm a/N) u t =
      (G (2*Real.pi*t)+G (-(2*Real.pi*t)))/2 := by
    rw [twistedCoprimeMellinMass_eq_divisor_mass S H U β hS u t hN]
    dsimp [G]
    congr 2 <;> congr 1 <;> ring
  simp_rw [hpoint]
  simpa only [f,G,arithmeticMellinCoefficient,neg_div,
    show (2:ℝ)*(2*Real.pi) = 4*Real.pi by ring] using he

end CubicFirstMoment

end

end OAI
