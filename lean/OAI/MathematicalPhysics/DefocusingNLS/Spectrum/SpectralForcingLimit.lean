import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralEventualCoefficientLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralBoundedCoefficientAction
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralBoundedPolynomialLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralResidualTailLimit

namespace OAI

/-! Assembly of the actual normalized forcing: the polynomial residual has
its free limit and the weighted coefficient error tends to zero. -/

open Filter Topology Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem circularCoefficientAction_real_smul (s : ℝ) (A B : ℂ) (z : E₄) :
    circularCoefficientAction ((s : ℂ)*A) ((s : ℂ)*B) z=
      s • circularCoefficientAction A B z := by
  apply Prod.ext <;> apply Prod.ext
  all_goals simp [circularCoefficientAction,Complex.real_smul,mul_assoc]

theorem boundedCircularCoefficientAction_factor (κ : ℝ) (νp νm η : ℂ) (m : ℕ)
    (q p : ℂ) (U : ℂ[X] × ℂ[X]) (A B : ℝ →ᵇ ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hA : A t=(Real.exp (κ*t) : ℂ)*
      (spectralDiagonalCoefficient m q-spectralDiagonalCoefficient m p))
    (hB : B t=(Real.exp (κ*t) : ℂ)*
      (spectralCrossCoefficient m q-spectralCrossCoefficient m p)) :
    Real.exp (-κ*t) •
      circularTailEvaluation (boundedCircularCoefficientAction A B (boundedCircularPolynomialJet U)) t=
        circularBoundedField νp νm η m q (circularPolynomialJet U t)-
          circularBoundedField νp νm η m p (circularPolynomialJet U t) := by
  rw [boundedCircularCoefficientAction_evaluation,boundedCircularPolynomialJet_eq U t ht,
    hA,hB,circularCoefficientAction_real_smul,smul_smul]
  have he : Real.exp (-κ*t)*Real.exp (κ*t)=1 := by
    rw [← Real.exp_add]
    simp
  rw [he,one_smul,circularBoundedField_coefficient_difference]

theorem exists_circular_normalized_forcing_limit
    (m : ℕ → ℕ) (hmTop : Tendsto m atTop atTop)
    (q p : ℕ → ℝ → ℂ) (hq : ∀ n, Continuous (q n)) (hp : ∀ n, Continuous (p n))
    (κ T ρ C : ℝ) (hT : 0 ≤ T) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C)
    (e : ℕ → ℝ →ᵇ ℂ)
    (he : ∀ᶠ n in atTop, 1 ≤ m n ∧ ‖e n‖ ≤ C ∧ ∀ t, T ≤ t →
      ‖q n t‖ ≤ ρ ∧ ‖p n t‖ ≤ ρ ∧
        q n t-p n t=(Real.exp (-κ*t) : ℂ)*e n t)
    (νp νm : ℕ → ℂ) (η : ℂ) (U : ℕ → ℂ[X] × ℂ[X]) (U₀ : ℂ[X] × ℂ[X])
    (hU : Tendsto (fun n => boundedCircularPolynomialJet (U n)) atTop
      (𝓝 (boundedCircularPolynomialJet U₀)))
    (r : ℕ → CircularTailSpace) (r₀ : CircularTailSpace) (hr : Tendsto r atTop (𝓝 r₀)) :
    ∃ f : ℕ → CircularTailSpace, Tendsto f atTop (𝓝 r₀) ∧
      ∀ᶠ n in atTop, ∀ t, T ≤ t → Real.exp (-κ*t) • circularTailEvaluation (f n) t=
        (circularBoundedField (νp n) (νm n) η (m n) (q n t) (circularPolynomialJet (U n) t)-
         circularBoundedField (νp n) (νm n) η (m n) (p n t) (circularPolynomialJet (U n) t))+
        Real.exp (-κ*t) • circularTailEvaluation (r n) t := by
  obtain ⟨A,B,hA,hB,hAB⟩ := exists_spectral_weighted_coefficient_limit_eventually
    m hmTop q p hq hp κ T ρ C hρ hρ1 hC e he
  let v := fun n => boundedCircularCoefficientAction (A n) (B n) (boundedCircularPolynomialJet (U n))
  have hv : Tendsto v atTop (𝓝 0) := boundedCircularCoefficientAction_tendsto_zero
    A B _ _ hA hB hU
  refine ⟨fun n => v n+r n,?_,?_⟩
  · simpa only [zero_add] using hv.add hr
  · filter_upwards [hAB] with n hn t ht
    change Real.exp (-κ*t) •
      (circularTailEvaluation (v n) t+circularTailEvaluation (r n) t)=_
    rw [smul_add]
    rw [boundedCircularCoefficientAction_factor κ (νp n) (νm n) η (m n)
      (q n t) (p n t) (U n) (A n) (B n) t (hT.trans ht)
      (hn t ht).1 (hn t ht).2]

end DefocusingNLS

end OAI
