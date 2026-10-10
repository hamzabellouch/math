import OAI.NumberTheory.CubicMoment.Angular.AngularNoncubeReflectedIntegral
import OAI.NumberTheory.CubicMoment.Estimates.MellinSignedIntegration

namespace OAI

/-! Both literal Poisson row signs, with a common range of exponents and
with the exact Fourier-to-arithmetic Jacobian. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_noncube_signed_mellin_integral_saving (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
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
      (1+ρ)^q*(∫ t : ℝ, ‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖*
        ((fullStructuredHeightMass R H 1 e ℓ u (W r) X (2*Real.pi*t)+
          fullStructuredHeightMass R H 1 e ℓ u (W r) X (-(2*Real.pi*t)))/2)) ≤
          K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η₁,σ₁,hη₁,hη₁',hσ₁,hplus⟩ := angular_noncube_mellin_integral_saving ℓ
    (γ := γ) (ι := ι) hSW hℓ hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ
    M hM V hV hV' k U q
  obtain ⟨η₂,σ₂,hη₂,hη₂',hσ₂,hminus⟩ := angular_noncube_mellin_reflected_integral_saving ℓ
    (γ := γ) (ι := ι) hSW hℓ hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ
    M hM V hV hV' k U q
  refine ⟨min η₁ η₂,min σ₁ σ₂,lt_min hη₁ hη₂,(min_le_left _ _).trans hη₁',
    lt_min hσ₁ hσ₂,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K₁,T₁,hK₁,hplus⟩ := hplus L W hL hW hlo hhi
  obtain ⟨K₂,T₂,hK₂,hminus⟩ := hminus L W hL hW hlo hhi
  refine ⟨(K₁+K₂)/(4*Real.pi),max T₁ T₂,by positivity,?_⟩
  intro r X B H e u ρ hT hprod hX hB hBL hH he heN hu hρ
  have hB₁ : B ≤ (L r)^(1+η₁) := hBL.trans
    (Real.rpow_le_rpow_of_exponent_le (hL r) (add_le_add le_rfl (min_le_left _ _)))
  have hB₂ : B ≤ (L r)^(1+η₂) := hBL.trans
    (Real.rpow_le_rpow_of_exponent_le (hL r) (add_le_add le_rfl (min_le_right _ _)))
  have he₁ : norm e ≤ (L r)^σ₁ := heN.trans
    (Real.rpow_le_rpow_of_exponent_le (hL r) (min_le_left _ _))
  have he₂ : norm e ≤ (L r)^σ₂ := heN.trans
    (Real.rpow_le_rpow_of_exponent_le (hL r) (min_le_right _ _))
  have hp := hplus r X B H e u ρ ((le_max_left _ _).trans hT)
    hprod hX hB hB₁ hH he he₁ hu hρ
  have hn := hminus r X B H e u ρ ((le_max_right _ _).trans hT)
    hprod hX hB hB₂ hH he he₂ hu hρ
  rw [normMellin_signed_height_integral]
  calc
    _ = ((1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖*
        fullStructuredHeightMass R H 1 e ℓ u (W r) X t)+
      (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ (-t)‖*
        fullStructuredHeightMass R H 1 e ℓ u (W r) X t))/(4*Real.pi) := by ring
    _ ≤ (K₁*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k+
        K₂*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k)/(4*Real.pi) :=
      div_le_div_of_nonneg_right (add_le_add hp hn) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
