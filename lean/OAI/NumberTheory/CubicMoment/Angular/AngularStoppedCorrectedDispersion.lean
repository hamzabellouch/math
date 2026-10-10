import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCoefficient
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedMixedLogSaving
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedMixedModel
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedSquarefreeModel
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCorrectedDispersion
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSquarefreeModel
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedMixedModel
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedMixedLogSaving
import OAI.NumberTheory.CubicMoment.Estimates.CorrectedDispersionTheorem

namespace OAI

/-! Corrected dispersion for the actual early-stopped coefficients. The
positive variance, its common-factor restoration, the squarefree mass,
and the product-squarefree mixed term are all derived arithmetic sums. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_corrected_dispersion_log_saving
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℝ) (hΦnn : ∀ x, 0 ≤ Φ x)
    (hΦ : HasCompactSupport (fun x => (Φ x:ℂ)))
    (hΦpos : tsupport (fun x => (Φ x:ℂ)) ⊆ Set.Ioi 0)
    (hΦ' : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)))
    {RΦ : ℝ} (hcut : ∀ x, RΦ < x → Φ x = 0) (k H : ℕ) :
    ∃ (K : ℝ) (G : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V A : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      b^(3/2:ℝ) ≤ A → A ≤ b^2/(Real.log X)^(3*(k+2*(2*k))) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower (1+δ) X h) →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early)
      correctedSquareMass S β u Φ A ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
  let Ψ := fun x => (Φ x:ℂ)
  obtain ⟨Kp,G₀,hKp,hpositive⟩ := angular_stopped_squarefree_model_log_saving (ι := ι) (E := E)
    hpnt hEF ℓ hℓ hMV hC hHuxley hξ hξz hκ hF hJ Ψ hΦ hΦpos hΦ' k H
  obtain ⟨Kt,hKt,htype⟩ := angular_stopped_corrected_mixed_log_saving ℓ (ι := ι)
    hVor Ψ hΦ hΦpos hΦ' hGamma hξ hξz hκ k
  obtain ⟨Km,hKm,hmodel⟩ := angular_stopped_mixed_model_log_saving ℓ (ι := ι)
    hξ hξz hκ Ψ hΦ hΦpos hΦ' k
  let G := max G₀ (k+1)
  refine ⟨Kp+2*(Kt+Km),G,by positivity,?_⟩
  filter_upwards [hpositive,htype,hmodel,eventually_ge_atTop (Real.exp 1)]
    with X hpositive htype hmodel hX
  intro δ b u V A hδ hδone hwidth hb hbXlo hbXhi hV hu hVF W hW hWi hWd
    hAlo hAhi e he hNe j₀ k₀ h Z Q early hj hR
  dsimp only
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  let T := squarefreeDivisorTruncation ((Real.log X)^(2*k))
  have hL1 : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hAp : 0 < A := (Real.rpow_pos_of_pos (by linarith : 0 < b) _).trans_le hAlo
  have hR₀ : 2*(Real.log X)^G₀ ≤ min (X^ξ) (geometricBinLower (1+δ) X h) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (le_max_left _ _)) (by norm_num)).trans hR
  have hR₁ : (Real.log X)^(k+1) ≤ min (X^ξ) (geometricBinLower (1+δ) X h) := by
    have hp := pow_le_pow_right₀ hL1 (le_max_right G₀ (k+1))
    have hn : 0 ≤ (Real.log X)^G := by positivity
    change 2*(Real.log X)^G ≤ _ at hR
    change (Real.log X)^(k+1) ≤ (Real.log X)^G at hp
    linarith
  have hp := hpositive δ b u V A hδ hδone hwidth hb hbXlo hbXhi hV hu hVF
    W hW hWi hWd hAlo hAhi e he hNe j₀ k₀ h Z Q early hj hR₀
  have ht := htype W hW
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early) e b A u hbXlo hbXhi hAlo
  have hm := hmodel δ b A u hδ hδone hbXlo hbXhi hAp W hW e
    j₀ k₀ h Z Q early hj hR₁
  have hmix := correction_mixed_error (dispersionModel S β u)
    (∑ r ∈ S, β r*normTwist u r*typeIMixedGauss r Ψ A)
    (mixedMassModel S β u Ψ A) (squarefreeModelMass Ψ A) _ _ ht hm
  have hT : ∀ d ∈ T, primary d := fun d hd => (mem_squarefreeDivisorTruncation.mp hd).1
  have hT1 : 1 ∈ T := mem_squarefreeDivisorTruncation.mpr
    ⟨primary_one,squarefree_one,by simpa only [norm_one_eq] using (one_le_pow₀ hL1)⟩
  have hS : ∀ r ∈ S, primary r := fun r hr => (stoppedIntervalSupport_spec X (b/2) b e hr).1
  apply (correctedSquareMass_le_of_errors T S hT hT1 hS β u Φ hΦnn hAp hcut _ _ hp hmix).trans_eq
  ring

end CubicFirstMoment

end

end OAI
