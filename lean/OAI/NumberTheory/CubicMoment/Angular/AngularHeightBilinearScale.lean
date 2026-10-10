import OAI.NumberTheory.CubicMoment.Estimates.HeightBilinearScale
import OAI.NumberTheory.CubicMoment.Angular.AngularHeightFullVariance
import OAI.NumberTheory.CubicMoment.Estimates.HeightBilinear
import OAI.NumberTheory.CubicMoment.Estimates.CorrectedBilinearScale
import OAI.NumberTheory.CubicMoment.Estimates.DispersionCutoff

namespace OAI

/-! Normalization of the genuine height-averaged bilinear estimate. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)

variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_rough_prime_height_bilinear
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R Q M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R) (hM : 0 ≤ M)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (k d : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (G : ℕ) (K L₀ : ℝ) (m : ℕ), 0 < K ∧
      ∀ (r : γ) (X : ι → ℝ) (A : ℝ) (e : Eisenstein) (u T : ℝ)
        (P : Finset Eisenstein) (α : Eisenstein → ℂ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
      T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) →
      (∀ a ∈ P, primary a ∧ norm a/A ∈ Set.Icc 1 Q) →
      (∑ a ∈ P, ‖α a‖^2) ≤ M*A*(1+Real.log (L r))^d →
      dyadicHeightMean (fun t =>
        ‖∑ a ∈ P, ∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
          α a*angularHeightPrimeCoefficient ℓ R (W r) X b*gauss (a*b)*normTwist (u+t) (a*b)‖) T ≤
        K*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hvar⟩ := angular_height_full_variance_saving ℓ
    (γ := γ) (ι := ι) hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ
    (fun x => (dispersionCutoff Q x:ℂ)) (dispersionCutoff_complex_compact Q)
    (dispersionCutoff_complex_smooth Q) (2*k+d)
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨G,K₀,L₀,m,hK₀,hvar⟩ := hvar L W hL hW hlo hhi
  refine ⟨G,2*(Real.sqrt (M*K₀)+1),L₀,m,by positivity,?_⟩
  intro r X A e u T P α hL₀ hprod hX hAlo hAhi he heN hT hThi hu hP henergy
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hTp : 0 < T := (pow_pos hz m).trans_le hT
  have hAp : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  let S := fullSquarefreePrimeSupport R (W r) X e
  let β := angularHeightPrimeCoefficient ℓ R (W r) X
  have hS : ∀ b ∈ S, primary b := fun b hb => (fullSquarefreePrimeSupport_primary R (W r) X e hb).1
  have hcont : Continuous (fun t => ∑ a ∈ P, ∑ b ∈ S,
      α a*β b*gauss (a*b)*normTwist (u+t) (a*b)) := by
    apply continuous_finsetSum
    intro a ha
    apply continuous_finsetSum
    intro b hb
    exact continuous_const.mul ((continuous_normTwist (a*b)).comp (continuous_const.add continuous_id))
  exact height_bilinear_error_log_saving hcont hTp hM hK₀.le hAp hLp hz k d
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (dyadicHeightMean_nonneg
      (((continuous_smoothedDispersionVariance S hS β (fun x => (dispersionCutoff Q x:ℂ))
        (dispersionCutoff_complex_compact Q) (dispersionCutoff_complex_smooth Q) hAp).comp
          (continuous_const.add continuous_id)).norm) hTp (fun _ => _root_.norm_nonneg _))
    (height_bilinear_full_variance_bound_sq P S α β u (fun a ha => (hP a ha).1) hS
      (dispersionCutoff Q) (dispersionCutoff_nonneg Q) (dispersionCutoff_complex_compact Q)
      (dispersionCutoff_complex_smooth Q) hAp hTp
      (fun a ha => (dispersionCutoff_one (hP a ha).2).ge))
    henergy (hvar r X A e u T hL₀ hprod hX hAlo hAhi he heN hT hThi hu)

end CubicFirstMoment

end

end OAI
