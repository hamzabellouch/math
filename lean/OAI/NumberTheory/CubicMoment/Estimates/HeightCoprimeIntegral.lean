import OAI.NumberTheory.CubicMoment.Estimates.HeightCoprimeContinuity
import OAI.NumberTheory.CubicMoment.Estimates.HeightSignedBound
import OAI.NumberTheory.CubicMoment.Estimates.LargeDivisorLogSaving
import OAI.NumberTheory.CubicMoment.Estimates.PrimeMassIntegral
import OAI.NumberTheory.CubicMoment.Estimates.NormMellinMoments

namespace OAI

/-! Full-line Mellin and independent height averaging for the actual
coprime Poisson mass. Every nonzero frequency and every common divisor
are included. The published hypotheses enter through the empty row. -/
noncomputable section
open MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem height_coprime_mellin_saving
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
      ∀ (r : γ) (X : ι → ℝ) (B : ℝ) (H P : Finset Eisenstein)
        (e : Eisenstein) (u T ρ N : ℝ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) → (∀ p ∈ P, primaryPrime p) →
      e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
      T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) → 0 ≤ ρ → 0 < N →
      (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
        ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖*
          twistedCoprimeMellinMass (fullSquarefreePrimeSupport R (W r) X e) H P
            (fullPrimeCoefficient R (W r) X) (fun a => norm a/N) (u+t) s) T ≤
        K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hempty⟩ := height_signed_mellin_saving
    (γ := γ) (ι := ι) hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ
    M hM V hV hV' k q
  obtain ⟨C₀,hC₀,hkernel⟩ := normDenominatorMellinCoefficient_moment_decay M hM V hV hV' q 0
  refine ⟨min η (c/4),σ,lt_min hη (by positivity),
    (min_le_left _ _).trans hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K₁,L₁,m,hK₁,hempty⟩ := hempty L W hL hW hlo hhi
  obtain ⟨K₂,L₂,hK₂,hlarge⟩ := fullPrime_large_divisor_log_saving hR hc hc₁ hW hlo hhi k
  refine ⟨K₁+2*K₂*C₀,max L₁ L₂,m,by positivity,?_⟩
  intro r X B H P e u T ρ N hL₀ hprod hX hB hBL hH hP he heN hT hThi hu hρ hN
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hTp : 0 < T := (pow_pos hz m).trans_le hT
  have hX₁ : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hX i).le
  have hrough : ∀ i, (L r)^c < X i := fun i =>
    (Real.rpow_le_rpow hLp.le (by linarith) hc.le).trans_lt (hX i)
  have hB₁ := hBL.trans (Real.rpow_le_rpow_of_exponent_le (hL r)
    (add_le_add le_rfl (min_le_left η (c/4))))
  have hB₂ := hBL.trans (Real.rpow_le_rpow_of_exponent_le (hL r)
    (add_le_add le_rfl (min_le_right η (c/4))))
  let f := fun s => ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖
  let A := K₂*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k
  let E := fun t => ∫ s : ℝ, f s*
    ((fullStructuredHeightMass R H 1 e 0 (u+t) (W r) X (2*Real.pi*s)+
      fullStructuredHeightMass R H 1 e 0 (u+t) (W r) X (-(2*Real.pi*s)))/2)
  have hfc : Continuous f := (𝓕 (normDenominatorLogSchwartz M hM V hV hV' ρ)).continuous.norm
  have hfi : Integrable f := (normDenominatorMellinCoefficient_integrable M hM V hV hV' ρ).norm
  have hEc : Continuous E := continuous_normMellin_signed_height_integral M hM V hV hV' R H e u ρ (W r) X
  have hmass := continuous_integral_twistedCoprimeMellinMass
    (fullSquarefreePrimeSupport R (W r) X e) H P
    (fun a ha => (fullSquarefreePrimeSupport_primary R (W r) X e ha).1)
    (fullPrimeCoefficient R (W r) X) (fun a => norm a/N) hfc hfi
  have havg := dyadicHeightMean_mono (hmass.comp (continuous_const.add continuous_id))
    (hEc.add continuous_const) hTp (fun t _ =>
      fullPrime_coprime_mass_integral_le (Real.one_le_rpow (hL r) hc.le)
        (W r) X (fun i => zero_lt_one.trans_le (hX₁ i)) (hlo r) (hhi r) hrough e H P hP (u+t) hN
        hfi (fun s => _root_.norm_nonneg _) (fun s =>
          hlarge r X B e H P (u+t) s N ((le_max_right _ _).trans hL₀)
            (hL r) hX₁ hprod hB hB₂ hH hP hN))
  simp only [Function.comp_def,Pi.add_apply,id_eq] at havg
  change dyadicHeightMean _ T ≤
    dyadicHeightMean (fun t => E t+A*(∫ s : ℝ, f s)) T at havg
  rw [dyadicHeightMean_add hEc continuous_const,dyadicHeightMean_const _ hTp.ne'] at havg
  have hs := hempty r X B H e u T ρ ((le_max_left _ _).trans hL₀)
    hprod hX hB hB₁ hH he heN hT hThi hu hρ
  have hk := hkernel ρ hρ
  simp only [pow_zero,one_mul] at hk
  calc
    _ ≤ (1+ρ)^q*(dyadicHeightMean E T+2*(A*(∫ s : ℝ, f s))) :=
      mul_le_mul_of_nonneg_left havg (by positivity)
    _ = (1+ρ)^q*dyadicHeightMean E T+2*A*((1+ρ)^q*(∫ s : ℝ, f s)) := by ring
    _ ≤ K₁*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k+2*A*C₀ :=
      add_le_add hs (mul_le_mul_of_nonneg_left hk (by dsimp [A]; positivity))
    _ = _ := by dsimp [A]; ring

end CubicFirstMoment

end

end OAI
