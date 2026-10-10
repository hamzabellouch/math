import OAI.NumberTheory.CubicMoment.Estimates.HeightCoprimeIntegral
import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeMellin

namespace OAI

/-! The actual norm-denominator Poisson form, on any nonzero frequency
annulus, averaged over an independent arithmetic height. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem height_radial_form_saving
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k q : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (K L₀ : ℝ) (m : ℕ), 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (B J : ℝ) (H : Finset Eisenstein)
        (e : Eisenstein) (u T ρ : ℝ) (phase : Eisenstein → ℂ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      1 ≤ B → B ≤ (L r)^(1+η) → 0 < J →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (∀ h ∈ H, J ≤ norm h ∧ norm h ≤ 2*J) → (∀ h ∈ H, ‖phase h‖ ≤ 1) →
      e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
      T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) → 0 ≤ ρ →
      (1+ρ)^q*dyadicHeightMean (fun t =>
        ‖normCoprimeRadialForm (fullSquarefreePrimeSupport R (W r) X e) H
          (fun a => star (fullPrimeCoefficient R (W r) X a*mellinPhase (u+t) (norm a)))
          (fun a => star (fullPrimeCoefficient R (W r) X a*mellinPhase (u+t) (norm a)))
          phase (fun h => norm h/J) (fun a => norm a/L r) V ρ‖) T ≤
        K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  let M := primeConvolutionLogRadius R (Fintype.card ι)
  have hM : 0 < M := primeConvolutionLogRadius_pos hR _
  obtain ⟨η,σ,hη,hη₁,hσ,hmass⟩ := height_coprime_mellin_saving
    (γ := γ) (ι := ι) hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ
    M hM V hV hV' k q
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K,L₀,m,hK,hmass⟩ := hmass L W hL hW hlo hhi
  refine ⟨K,L₀,m,hK,?_⟩
  intro r X B J H e u T ρ phase hL₀ hprod hX hB hBL hJ hH hHJ hphase he heN hT hThi hu hρ
  let S := fullSquarefreePrimeSupport R (W r) X e
  let P := S.biUnion primaryPrimeFactors
  let v := fun t (a : Eisenstein) => star (fullPrimeCoefficient R (W r) X a*mellinPhase (u+t) (norm a))
  have hvc (a : Eisenstein) : Continuous (fun t => v t a) := by
    dsimp [v,mellinPhase]
    fun_prop
  have hS : ∀ a ∈ S, primary a ∧ Squarefree a :=
    fun a ha => fullSquarefreePrimeSupport_primary R (W r) X e ha
  have hP : ∀ p ∈ P, primaryPrime p := by
    intro p hp
    obtain ⟨a,ha,hpa⟩ := Finset.mem_biUnion.mp hp
    exact (primaryPrimeFactor_spec (hS a ha).1 hpa).1
  have hSP : ∀ a ∈ S, primaryPrimeFactors a ⊆ P := by
    intro a ha p hp
    exact Finset.mem_biUnion.mpr ⟨a,ha,hp⟩
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hTp : 0 < T := (pow_pos hz m).trans_le hT
  have hXpos : ∀ i, 0 < X i := fun i => lt_of_lt_of_le zero_lt_one
    ((Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hX i).le)
  have hlog := fullPrimeMellin_log_range hR hJ (W r) X hXpos (hlo r) (hhi r) e H hHJ
  rw [hprod] at hlog
  have hn (t : ℝ) := normCoprimeRadialForm_norm_le_mass M hM S H P hS hP hSP
    (v t) (v t) phase hphase (fun h => norm h/J) (fun a => norm a/L r)
    (fun h hh => (le_div_iff₀ hJ).mpr (by simpa using (hHJ h hh).1))
    (fun a ha => div_pos (norm_pos_of_ne_zero (primary_ne_zero (hS a ha).1)) hLp)
    hlog V hV hV' hρ
  have hf := normCoprimeRadialForm_continuous_coefficients S H v v hvc hvc
    phase (fun h => norm h/J) (fun a => norm a/L r) V ρ
  have hg := continuous_integral_twistedCoprimeMellinMass S H P
    (fun a ha => (hS a ha).1) (fullPrimeCoefficient R (W r) X) (fun a => norm a/L r)
    (𝓕 (normDenominatorLogSchwartz M hM V hV hV' ρ)).continuous.norm
    (normDenominatorMellinCoefficient_integrable M hM V hV hV' ρ).norm
  have hh := dyadicHeightMean_mono hf.norm (hg.comp (continuous_const.add continuous_id)) hTp
    (fun t _ => hn t)
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans
    (hmass r X B H P e u T ρ (L r) hL₀ hprod hX hB hBL hH hP he heN hT hThi hu hρ hLp)

end CubicFirstMoment

end

end OAI
