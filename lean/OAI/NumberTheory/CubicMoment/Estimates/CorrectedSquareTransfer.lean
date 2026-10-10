import OAI.NumberTheory.CubicMoment.Estimates.CorrectedSquareMass
import OAI.NumberTheory.CubicMoment.Estimates.MixedTermIdentity

namespace OAI

/-! Transfer the proved complex variance and Type-I estimates to the
actual nonnegative corrected square. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem correctedSquareMass_le_of_errors (C S : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c) (h1 : 1 ∈ C) (hS : ∀ b ∈ S, primary b)
    (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x)
    {A R : ℝ} (hA : 0 < A) (hcut : ∀ x, R < x → V x = 0)
    (E₁ E₂ : ℝ)
    (hvariance : ‖sievedDispersionVariance C S β u (fun x => (V x:ℂ)) A-
      ((cStar^2*‖dispersionModel S β u‖^2:ℝ):ℂ)*
        squarefreeModelMass (fun x => (V x:ℂ)) A‖ ≤ E₁)
    (hmixed : ‖((cStar:ℂ)*star (dispersionModel S β u))*
      (∑ b ∈ S, β b*normTwist u b*typeIMixedGauss b (fun x => (V x:ℂ)) A)-
      ((cStar^2*‖dispersionModel S β u‖^2:ℝ):ℂ)*
        squarefreeModelMass (fun x => (V x:ℂ)) A‖ ≤ E₂) :
    correctedSquareMass S β u V A ≤ E₁+2*E₂ := by
  have hmodel : ((cStar^2*‖dispersionModel S β u‖^2:ℝ):ℂ)*
      squarefreeModelMass (fun x => (V x:ℂ)) A =
      (((cStar^2*‖dispersionModel S β u‖^2)*
        (∑ a ∈ primaryElementBall (R*A), (idealMoebius a:ℝ)^2*V (norm a/A)*
          norm a^(-1/3:ℝ)):ℝ):ℂ) := by
    rw [squarefreeModelMass_ofReal V hA le_rfl hcut]
    push_cast
    rfl
  have hp := hvariance
  rw [sievedDispersionVariance_ofReal C S β u V hA le_rfl hcut,hmodel,
    ←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hp
  have hm := hmixed
  rw [typeIMixedGauss_sum_eq S hS β u (fun x => (V x:ℂ)) hA le_rfl
    (fun x hx => by rw [hcut x hx]; rfl),hmodel] at hm
  rw [correctedSquareMass_eq_sum S β u V hA le_rfl hcut]
  exact corrected_dispersion_finite_error _ C S
    (fun a ha => (mem_primaryElementBall.mp ha).1) hC h1
    (fun a => V (norm a/A)) (fun a _ => hV _) β u E₁ E₂ hp hm

end CubicFirstMoment

end

end OAI
