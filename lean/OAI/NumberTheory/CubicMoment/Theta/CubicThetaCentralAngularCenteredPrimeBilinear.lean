import OAI.NumberTheory.CubicMoment.Angular.AngularCenteredPrimeBilinear
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralAngularCorrectedPrimeBilinear

namespace OAI

/-! The rough-prime bilinear theorem for the original centered kernel,
with the true squarefree product weight. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]


theorem angular_rough_prime_centered_bilinear_actual
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C c R Q M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R) (hQ : 1 ≤ Q) (hM : 0 ≤ M)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
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
      ‖∑ a ∈ P, ∑ b ∈ fullSquarefreePrimeSupport R (W r) X e,
          α a*angularHeightPrimeCoefficient ℓ R (W r) X b*centeredGauss (a*b)*normTwist u (a*b)‖ ≤
        K*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,G,K₁,T₁,hη,hη1,hσ,hK₁,hcorrected⟩ :=
    angular_rough_prime_corrected_bilinear_actual ℓ (Q := Q) hSW hℓ hpub hHuxley hperiod hMV hC hc hc1 hR hM
      hGI hGQ  hGamma L W hL hW hlo hhi k d U
  obtain ⟨K₂,T₂,hK₂,hoverlap⟩ := angular_full_prime_model_overlap_log_saving ℓ
    hW hR (zero_le_one.trans hQ) hc hM hlo hhi k d
  refine ⟨η,σ,G,K₁+K₂,max T₁ T₂,hη,hη1,hσ,by positivity,?_⟩
  intro r X A e u P α hT hprod hrough hAlo hAhi he heN hu hP hα
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hA : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  have hX : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hrough i).le
  have hh₁ := hcorrected r X A e u P α ((le_max_left _ _).trans hT)
    hprod hrough hAlo hAhi he heN hu hP hα
  have hh₂ := hoverlap r X e u A P α ((le_max_right _ _).trans hT) (hL r) hX hprod
    (fun i => (Real.rpow_le_rpow hLp.le (by linarith) hc.le).trans_lt (hrough i)) hA
    (fun a ha => ⟨(hP a ha).1,
      by simpa only [one_mul] using (le_div_iff₀ hA).mp (hP a ha).2.1,
      (div_le_iff₀ hA).mp (hP a ha).2.2⟩) hα
  rw [centered_bilinear_eq_correction_add_overlap P _ α _ u (fun a ha => (hP a ha).1)
    (fun b hb => fullSquarefreePrimeSupport_primary R (W r) X e hb)]
  exact (norm_add_le _ _).trans ((add_le_add hh₁ hh₂).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
