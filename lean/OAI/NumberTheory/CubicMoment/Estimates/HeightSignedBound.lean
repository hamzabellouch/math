import OAI.NumberTheory.CubicMoment.Estimates.HeightSignedMellin
import OAI.NumberTheory.CubicMoment.Estimates.HeightAllFrequencyMellin

namespace OAI

/-! Both signed empty-divisor Poisson rows have the required height
mean over the full Mellin line. Cube frequencies are included. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem height_signed_mellin_saving
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (k q : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (K L₀ : ℝ) (m : ℕ), 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (B : ℝ) (H : Finset Eisenstein)
        (e : Eisenstein) (u T ρ : ℝ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
      T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) → 0 ≤ ρ →
      (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
        ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖*
        ((fullStructuredHeightMass R H 1 e 0 (u+t) (W r) X (2*Real.pi*s)+
          fullStructuredHeightMass R H 1 e 0 (u+t) (W r) X (-(2*Real.pi*s)))/2)) T ≤
        K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hmean⟩ := height_all_frequency_mellin_saving
    (γ := γ) (ι := ι) hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ
    M hM V hV hV' k q
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K,L₀,m,hK,hmean⟩ := hmean L W hL hW hlo hhi
  refine ⟨K/(2*Real.pi),L₀,m,by positivity,?_⟩
  intro r X B H e u T ρ hL₀ hprod hX hB hBL hH he heN hT hThi hu hρ
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hTp : 0 < T := (pow_pos hz m).trans_le hT
  have hp := hmean r X B H e u T ρ 1 hL₀ hprod hX hB hBL hH he heN hT hThi hu hρ (Or.inl rfl)
  have hn := hmean r X B H e u T ρ (-1) hL₀ hprod hX hB hBL hH he heN hT hThi hu hρ (Or.inr rfl)
  simp only [one_mul] at hp
  simp only [neg_one_mul] at hn
  rw [normMellin_signed_height_average M hM V hV hV' R H e u ρ (W r) X hTp]
  calc
    _ = ((1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
          ‖arithmeticMellinCoefficient M hM V hV hV' ρ s‖*
            fullStructuredHeightMass R H 1 e 0 0 (W r) X (t+u+s)) T+
        (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
          ‖arithmeticMellinCoefficient M hM V hV hV' ρ (-s)‖*
            fullStructuredHeightMass R H 1 e 0 0 (W r) X (t+u+s)) T)/(4*Real.pi) := by ring
    _ ≤ (K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k+
          K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k)/(4*Real.pi) :=
      div_le_div_of_nonneg_right (add_le_add hp hn) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
