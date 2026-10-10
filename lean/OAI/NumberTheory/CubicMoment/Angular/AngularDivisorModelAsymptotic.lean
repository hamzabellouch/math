import OAI.NumberTheory.CubicMoment.Angular.AngularDivisorNoncubeTotal
import OAI.NumberTheory.CubicMoment.Angular.AngularHeightDivisorBounds
import OAI.NumberTheory.CubicMoment.Angular.AngularDivisorGramAsymptotic
import OAI.NumberTheory.CubicMoment.Angular.AngularCubeModelLogSaving

namespace OAI

/-! Restore all pairs in the model polynomial of the square-divisor
coprime variance. The model is now the literal squared finite sum. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_divisor_coprime_model_asymptotic (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
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
      ‖divisorCoprimeDispersionGram d (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A -
        (1/(norm d)^2:ℝ)*cubeModelTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hgram⟩ := angular_divisor_coprime_gram_asymptotic ℓ
    (γ := γ) (ι := ι) hSW hℓ hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ V hV hV' k U
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨G,K₁,T₁,hK₁,hgram⟩ := hgram L W hL hW hlo hhi
  obtain ⟨K₂,T₂,hK₂,hmodel⟩ := angular_cube_model_overlap_log_saving ℓ hR hc hW hlo hhi V k
  refine ⟨G,K₁+K₂,max T₁ T₂,by positivity,?_⟩
  intro r X A d e u hT hprod hrough hd hds hdη hdc hAlo hAhi he heN hu
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hA : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  have hX : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith [hL r] : (1:ℝ) ≤ 2*L r) hc.le).trans (hrough i).le
  have hrough' : ∀ i, (L r)^c < X i := fun i =>
    (Real.rpow_le_rpow hLp.le (by linarith) hc.le).trans_lt (hrough i)
  have hg := hgram r X A d e u ((le_max_left _ _).trans hT) hprod hrough hd hds hdη hdc
    hAlo hAhi he heN hu
  have hm := hmodel r X A e u ((le_max_right _ _).trans hT) (hL r) hX hprod hrough' hA.le
  have hcoeff : 1/(norm d)^2 ≤ 1 := by
    simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1)
      (one_le_pow₀ (one_le_norm (primary_ne_zero hd)) : 1 ≤ (norm d)^2)
  have hm' :
      ‖(1/(norm d)^2:ℝ)*
        (coprimeCubeMainTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A -
        cubeModelTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A)‖ ≤
      K₂*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ 1/(norm d)^2 by positivity),
      norm_sub_rev]
    exact (mul_le_of_le_one_left (_root_.norm_nonneg _) hcoeff).trans hm
  calc
    _ = ‖(divisorCoprimeDispersionGram d (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A -
        (1/(norm d)^2:ℝ)*coprimeCubeMainTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A) +
        (1/(norm d)^2:ℝ)*(coprimeCubeMainTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A -
        cubeModelTerm (fullSquarefreePrimeSupport R (W r) X e)
          (angularHeightPrimeCoefficient ℓ R (W r) X) u V A)‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans ((add_le_add hg hm').trans_eq (by ring))

end CubicFirstMoment

end

end OAI
