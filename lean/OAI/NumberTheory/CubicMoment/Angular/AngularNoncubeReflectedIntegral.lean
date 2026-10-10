import OAI.NumberTheory.CubicMoment.Angular.AngularNoncubeMellinIntegral
import OAI.NumberTheory.CubicMoment.Estimates.MellinConjugation

namespace OAI

/-! The full noncube integral estimate for the reflected radial kernel.
This is deduced by conjugating the original smooth weight. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_noncube_mellin_reflected_integral_saving (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (k U q : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (B : ℝ)
      (H : Finset Eisenstein) (e : Eisenstein) (u ρ : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ z : Eisenstein, z^3 = h) →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U → 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ (-t)‖*
        fullStructuredHeightMass R H 1 e ℓ u (W r) X t) ≤
          K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  have hVc : HasCompactSupport (fun x => star (V x)) :=
    hV.comp_left (show star (0:ℂ) = 0 from star_zero _)
  have hVc' : ContDiff ℝ ∞ (fun x => star (V x)) :=
    Complex.conjCLE.contDiff.comp hV'
  have he := angular_noncube_mellin_integral_saving ℓ (γ := γ) (ι := ι)
    hSW hℓ hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ
    M hM (fun x => star (V x)) hVc hVc' k U q
  simpa only [arithmeticMellinCoefficient_conj M hM V hV hV' hVc hVc',norm_star] using he

end CubicFirstMoment

end

end OAI
