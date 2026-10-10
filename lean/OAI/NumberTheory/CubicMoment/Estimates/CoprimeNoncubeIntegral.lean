import OAI.NumberTheory.CubicMoment.Estimates.LargeDivisorLogSaving
import OAI.NumberTheory.CubicMoment.Estimates.PrimeMassIntegral
import OAI.NumberTheory.CubicMoment.Estimates.SignedNoncubeIntegral
import OAI.NumberTheory.CubicMoment.Estimates.NormMellinMoments

namespace OAI

/-! The actual coprime Poisson mass has a full-line logarithmic saving.
Both signs and all common divisors are retained. Published inputs occur
only in the already proved empty-row noncube estimate. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem coprime_noncube_mellin_integral_saving (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (k U q : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (B : ℝ)
      (H P : Finset Eisenstein) (e : Eisenstein) (u ρ N : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ z : Eisenstein, z^3 = h) →
      (∀ p ∈ P, primaryPrime p) →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U → 0 ≤ ρ → 0 < N →
      (1+ρ)^q*(∫ t : ℝ, ‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖*
        coprimeMellinMass (fullSquarefreePrimeSupport R (W r) X e) H P
          (fun a => star (fullPrimeCoefficient R (W r) X a*mellinPhase u (norm a)))
          (fun a => star (fullPrimeCoefficient R (W r) X a*mellinPhase u (norm a)))
          (fun a => norm a/N) t) ≤
          K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hempty⟩ := noncube_signed_mellin_integral_saving
    (γ := γ) (ι := ι) hSW hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ
    M hM V hV hV' k U q
  obtain ⟨C₀,hC₀,hkernel⟩ := normDenominatorMellinCoefficient_moment_decay M hM V hV hV' q 0
  refine ⟨min η (c/4),σ,lt_min hη (by positivity),
    (min_le_left _ _).trans hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K₁,T₁,hK₁,hempty⟩ := hempty L W hL hW hlo hhi
  obtain ⟨K₂,T₂,hK₂,hlarge⟩ := fullPrime_large_divisor_log_saving hR hc hc₁ hW hlo hhi k
  refine ⟨K₁+K₂*C₀,max T₁ T₂,by positivity,?_⟩
  intro r X B H P e u ρ N hT hprod hX hB hBL hH hP he heN hu hρ hN
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hX₁ : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hX i).le
  have hrough : ∀ i, (L r)^c < X i := fun i =>
    (Real.rpow_le_rpow hLp.le (by linarith) hc.le).trans_lt (hX i)
  have hB₁ := hBL.trans (Real.rpow_le_rpow_of_exponent_le (hL r)
    (add_le_add le_rfl (min_le_left η (c/4))))
  have hB₂ := hBL.trans (Real.rpow_le_rpow_of_exponent_le (hL r)
    (add_le_add le_rfl (min_le_right η (c/4))))
  have hs := hempty r X B H e u ρ ((le_max_left _ _).trans hT)
    hprod hX hB hB₁ hH he heN hu hρ
  have hl := fun t => hlarge r X B e H P u t N ((le_max_right _ _).trans hT)
    (hL r) hX₁ hprod hB hB₂ (fun h hh => ⟨(hH h hh).1,(hH h hh).2.1⟩) hP hN
  have hi := fullPrime_coprime_mass_integral_le (Real.one_le_rpow (hL r) hc.le)
    (W r) X (fun i => zero_lt_one.trans_le (hX₁ i)) (hlo r) (hhi r) hrough e H P hP u hN
    (normDenominatorMellinCoefficient_integrable M hM V hV hV' ρ).norm
    (fun _ => _root_.norm_nonneg _) hl
  have hk := hkernel ρ hρ
  simp only [pow_zero,one_mul] at hk
  calc
    _ ≤ (1+ρ)^q*((∫ t : ℝ, ‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖*
        ((fullStructuredHeightMass R H 1 e 0 u (W r) X (2*Real.pi*t)+
          fullStructuredHeightMass R H 1 e 0 u (W r) X (-(2*Real.pi*t)))/2))+
        (K₂*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k)*
          (∫ t : ℝ, ‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = (1+ρ)^q*(∫ t : ℝ, ‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖*
        ((fullStructuredHeightMass R H 1 e 0 u (W r) X (2*Real.pi*t)+
          fullStructuredHeightMass R H 1 e 0 u (W r) X (-(2*Real.pi*t)))/2))+
        (K₂*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k)*
          ((1+ρ)^q*(∫ t : ℝ, ‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖)) := by ring
    _ ≤ K₁*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k+
        (K₂*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k)*C₀ :=
      add_le_add hs (mul_le_mul_of_nonneg_left hk (by positivity))
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
