import OAI.NumberTheory.CubicMoment.Angular.AngularCorrectedDispersionTheorem
import OAI.NumberTheory.CubicMoment.Estimates.CorrectedBilinearScale
import OAI.NumberTheory.CubicMoment.Estimates.DispersionCutoff

namespace OAI

/-! A logarithmic bilinear saving for the actual independent prime
convolution. This uses only the explicitly cited published inputs. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_rough_prime_corrected_bilinear
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C c R Q M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R) (hM : 0 ≤ M)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (L : γ → ℝ) (W : γ → ι → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    (hhi : ∀ r i x, R < x → W r i x = 0) (k d U : ℕ) :
    ∃ (η σ : ℝ) (G : ℕ) (K T₀ : ℝ), 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧ 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (A : ℝ) (e : Eisenstein) (u : ℝ)
        (P : Finset Eisenstein) (α : Eisenstein → ℂ),
      T₀ ≤ L r → (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      (L r)^(1-η/16) ≤ A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U →
      (∀ a ∈ P, primary a ∧ norm a/A ∈ Set.Icc 1 Q) →
      (∑ a ∈ P, ‖α a‖^2) ≤ M*A*(1+Real.log (L r))^d →
      ‖correctedBilinearSum P (fullSquarefreePrimeSupport R (W r) X e)
          α (angularHeightPrimeCoefficient ℓ R (W r) X) u‖ ≤
        K*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,G,K₀,T₀,hη,hη1,hσ,hK₀,hvariance⟩ :=
    angular_corrected_dispersion_asymptotic ℓ hSW hℓ hpub hHuxley hperiod hMV hC hc hc1 hR hGI hGQ
      hVor hGamma L W hL hW hlo hhi (dispersionCutoff Q) (dispersionCutoff_nonneg Q)
      (dispersionCutoff_complex_compact Q) (dispersionCutoff_positive_support Q)
      (dispersionCutoff_complex_smooth Q) (fun _ hx => dispersionCutoff_high hx) (2*k+d) U
  refine ⟨η,σ,G,Real.sqrt (M*K₀)+1,T₀,hη,hη1,hσ,by positivity,?_⟩
  intro r X A e u P α hT hprod hrough hAlo hAhi he heN hu hP henergy
  have hAp : 0 < A := (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hL r)) _).trans_le hAlo
  have hm := hvariance r X A e u hT hprod hrough hAlo hAhi he heN hu
  have hb := corrected_bilinear_log_saving P (fullSquarefreePrimeSupport R (W r) X e)
    α (angularHeightPrimeCoefficient ℓ R (W r) X) u (fun a ha => (hP a ha).1)
    (fun b hb => (fullSquarefreePrimeSupport_primary R (W r) X e hb).1)
    (dispersionCutoff Q) (dispersionCutoff_nonneg Q) hAp
    (zero_lt_one.trans_le (hL r)) (by linarith [Real.log_nonneg (hL r)]) hM hK₀.le
    (fun _ hx => dispersionCutoff_high hx)
    (fun a ha => (dispersionCutoff_one (hP a ha).2).ge) k d henergy hm
  apply hb.trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : Real.sqrt (M*K₀) ≤ Real.sqrt (M*K₀)+1)
        (Real.rpow_nonneg hAp.le _)) (Real.rpow_nonneg (zero_le_one.trans (hL r)) _))
    (pow_nonneg (by linarith [Real.log_nonneg (hL r)]) _)

end CubicFirstMoment

end

end OAI
