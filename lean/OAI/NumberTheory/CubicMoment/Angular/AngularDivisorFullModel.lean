import OAI.NumberTheory.CubicMoment.Angular.AngularDivisorNoncubeTotal
import OAI.NumberTheory.CubicMoment.Angular.AngularHeightDivisorBounds
import OAI.NumberTheory.CubicMoment.Angular.AngularDivisorModelAsymptotic
import OAI.NumberTheory.CubicMoment.Estimates.CommonOuterLogSaving

namespace OAI

/-! The full small-square-divisor variance has the literal squared
model. This adds the proved noncoprime remainder to the coprime model. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_divisor_full_model_asymptotic (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k U : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (G : ℕ) (K T₀ : ℝ), 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A : ℝ)
      (d e : Eisenstein) (u : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      primary d → Squarefree d → norm d ≤ (L r)^(η/16) → norm d ≤ (L r)^c →
      (L r)^(1-η/16) ≤ A → A ≤ (L r)^2/(1+Real.log (L r))^G →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U →
      ‖divisorDispersionVariance d (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A-
        (1/(norm d)^2:ℝ)*cubeModelTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η₀,σ,hη₀,hη₀1,hσ,hgram⟩ := angular_divisor_coprime_model_asymptotic ℓ
    (γ := γ) (ι := ι) hSW hℓ hpub hHuxley hperiod hMV hC hc hc1 hR hGI hGQ V hV hV' k U
  let η := min η₀ c
  have hη : 0 < η := lt_min hη₀ hc
  have hη0 : η ≤ η₀ := min_le_left _ _
  have hηc : η ≤ c := min_le_right _ _
  have hη1 : η ≤ 1 := hη0.trans hη₀1
  refine ⟨η,σ,hη,hη1,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨G₁,K₁,T₁,hK₁,hgram⟩ := hgram L W hL hW hlo hhi
  obtain ⟨G₂,K₂,T₂,hK₂,hcommon⟩ := angular_fullPrime_divisor_noncoprime_log_saving ℓ
    hR hc hc1 (show η/16 ≤ c by linarith) hW hlo hhi V hV hV' k
  refine ⟨G₁+G₂,K₁+K₂,max T₁ T₂,by positivity,?_⟩
  intro r X A d e u hT hprod hrough hd hds hdη hdc hAlo hAhi he heN hu
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hz1 : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hz : 0 < 1+Real.log (L r) := zero_lt_one.trans_le hz1
  have hcut (n : ℕ) (hn : n ≤ G₁+G₂) : A ≤ (L r)^2/(1+Real.log (L r))^n :=
    hAhi.trans (div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hz n)
      (pow_le_pow_right₀ hz1 hn))
  have hX : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hrough i).le
  have hrough' : ∀ i, (L r)^c < X i := fun i =>
    (Real.rpow_le_rpow hLp.le (by linarith) hc.le).trans_lt (hrough i)
  have hdL : norm d ≤ L r := hdη.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (hL r) (show η/16 ≤ 1 by linarith))
  have hc' := hcommon r X A d e u ((le_max_right _ _).trans hT) (hL r) hX hprod
    hrough' hd hdL hAlo (hcut G₂ (Nat.le_add_left _ _))
  have hg := hgram r X A d e u ((le_max_left _ _).trans hT) hprod hrough hd hds
    (hdη.trans (Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith))) hdc
    ((Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith)).trans hAlo)
    (hcut G₁ (Nat.le_add_right _ _)) he heN hu
  have htri : ∀ a b c : ℂ, ‖a-c‖ ≤ ‖a-b‖+‖b-c‖ := by
    intro a b c
    calc
      _ = ‖(a-b)+(b-c)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  exact (htri _ _ _).trans ((add_le_add hc' hg).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
