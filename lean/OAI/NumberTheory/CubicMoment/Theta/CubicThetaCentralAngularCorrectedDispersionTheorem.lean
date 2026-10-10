import OAI.NumberTheory.CubicMoment.Angular.AngularCorrectedDispersionTheorem
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralAngularTypeIMixedLogSaving

namespace OAI

/-! The complete corrected dispersion estimate. The positive variance,
Type-I mixed term and squarefree model are actual arithmetic sums. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)

variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]


theorem angular_corrected_dispersion_asymptotic_actual
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (L : γ → ℝ) (W : γ → ι → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0)
    (V : ℝ → ℝ) (hVnn : ∀ x, 0 ≤ V x)
    (hV : HasCompactSupport (fun x => (V x:ℂ)))
    (hVp : tsupport (fun x => (V x:ℂ)) ⊆ Set.Ioi 0)
    (hVs : ContDiff ℝ ∞ (fun x => (V x:ℂ)))
    {Rᵥ : ℝ} (hcut : ∀ x, Rᵥ < x → V x = 0) (k U : ℕ) :
    ∃ (η σ : ℝ) (G : ℕ) (K T₀ : ℝ), 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧ 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (A : ℝ) (e : Eisenstein) (u : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      (L r)^(1-η/16) ≤ A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U →
      correctedSquareMass (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η₀,σ,b,G,Kp,Tp,hη₀,hη₀1,hσ,hKp,hpositive⟩ :=
    angular_sieved_squarefree_model_asymptotic ℓ hSW hℓ hpub hHuxley hperiod hMV hC hc hc1 hR
      hGI hGQ L W hL hW hlo hhi (fun x => (V x:ℂ)) hV hVp hVs k U
  obtain ⟨Kt,Tt,hKt,htype⟩ := angular_logarithmic_typeI_corrected_mixed_actual ℓ
     hW hR hlo hhi (fun x => (V x:ℂ)) hV hVp hVs hGamma k
  obtain ⟨Kc,Tc,hKc,hcoprime⟩ := angular_mixed_model_coprimality_log_saving ℓ
    hW hR hc hlo hhi (fun x => (V x:ℂ)) hV hVp hVs k
  let η := min η₀ (1/100)
  refine ⟨η,σ,G,Kp+2*(Kt+Kc),max Tp (max Tt Tc),
    lt_min hη₀ (by norm_num), (min_le_left _ _).trans hη₀1,hσ,by positivity,?_⟩
  intro r X A e u hT hprod hrough hAlo hAhi he heN hu
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hX : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hrough i).le
  have hA₀ : (L r)^(1-η₀/16) ≤ A :=
    (Real.rpow_le_rpow_of_exponent_le (hL r) (by dsimp [η]; linarith [min_le_left η₀ (1/100)])).trans hAlo
  have hA99 : (L r)^(99/100:ℝ) ≤ A :=
    (Real.rpow_le_rpow_of_exponent_le (hL r) (by dsimp [η]; linarith [min_le_right η₀ (1/100)])).trans hAlo
  have hAp : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  have hp := hpositive r X A e u ((le_max_left _ _).trans hT)
    hprod hrough hA₀ hAhi he heN hu
  have ht := htype r X e u A ((le_max_left _ _).trans ((le_max_right _ _).trans hT))
    (hL r) hX hprod hA99
  have hc' := hcoprime r X e u A ((le_max_right _ _).trans ((le_max_right _ _).trans hT))
    (hL r) hX hprod (fun i =>
      (Real.rpow_le_rpow hLp.le (by linarith) hc.le).trans_lt (hrough i)) hAp
  have hm := correction_mixed_error _ _ _ _ _ _ ht hc'
  let D := squarefreeDivisorTruncation ((1+Real.log (L r))^b)
  have hD : ∀ d ∈ D, primary d := fun d hd => (mem_squarefreeDivisorTruncation.mp hd).1
  have hD1 : 1 ∈ D := mem_squarefreeDivisorTruncation.mpr
    ⟨primary_one,squarefree_one,by simpa only [norm_one_eq] using
      (one_le_pow₀ (by linarith [Real.log_nonneg (hL r)] : (1:ℝ) ≤ 1+Real.log (L r)))⟩
  have hS : ∀ z ∈ fullSquarefreePrimeSupport R (W r) X e, primary z :=
    fun z hz => (fullSquarefreePrimeSupport_primary R (W r) X e hz).1
  apply (correctedSquareMass_le_of_errors D _ hD hD1 hS _ u V hVnn hAp hcut _ _ hp hm).trans_eq
  ring

end CubicFirstMoment

end

end OAI
