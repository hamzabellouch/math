import OAI.NumberTheory.CubicMoment.Estimates.DivisorPoissonSplit
import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeSmallCoprime
import OAI.NumberTheory.CubicMoment.Estimates.CubeLogSaving

namespace OAI

/-! The coprime component of the actual square-divisor variance has
the same cube model, multiplied by its exact divisor density. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem divisor_coprime_gram_asymptotic (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
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
          (fullPrimeCoefficient R (W r) X) u V A -
        (1/(norm d)^2:ℝ)*coprimeCubeMainTerm (fullSquarefreePrimeSupport R (W r) X e)
          (fullPrimeCoefficient R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hnoncube⟩ := divisor_noncube_total_saving
    (γ := γ) (ι := ι) hSW hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ V hV hV' k U
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨Kn,Tn,hKn,hn⟩ := hnoncube L W hL hW hlo hhi
  obtain ⟨G,Kc,Tc,hKc,hcube⟩ := cube_poisson_log_saving hR hc hW hlo hhi V hV hV' k
  refine ⟨G,Kn+Kc,max 2 (max Tn Tc),by positivity,?_⟩
  intro r X A d e u hT hprod hrough hd hds hdη hdc hAlo hAhi he heN hu
  have hd0 := primary_ne_zero hd
  have hd1 : 1 ≤ norm d := one_le_norm hd0
  have h2 : 2 ≤ L r := (le_max_left _ _).trans hT
  have hLp : 0 < L r := by linarith
  have hz : 1 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hAp : 0 < A := (Real.rpow_pos_of_pos hLp _).trans_le hAlo
  have hA₂ : A ≤ (L r)^2 := hAhi.trans (div_le_self (sq_nonneg _) (one_le_pow₀ hz))
  have hX : ∀ i, 1 ≤ X i := fun i =>
    (Real.one_le_rpow (by linarith : (1:ℝ) ≤ 2*L r) hc.le).trans (hrough i).le
  have hrough' : ∀ i, (L r)^c < X i := fun i =>
    (Real.rpow_le_rpow hLp.le (by linarith) hc.le).trans_lt (hrough i)
  have hS (a : Eisenstein) (ha : a ∈ fullSquarefreePrimeSupport R (W r) X e) :
      primary a ∧ Squarefree a ∧ a ≠ 1 := by
    have hp := fullSquarefreePrimeSupport_primary R (W r) X e ha
    refine ⟨hp.1,hp.2,?_⟩
    have hb := (fullPrimeProduct_norm_bounds R (W r) X
      (fun i => zero_lt_one.trans_le (hX i)) (hlo r) (hhi r) (Finset.mem_filter.mp ha).1).1
    rw [hprod] at hb
    intro ha1
    rw [ha1,norm_one_eq] at hb
    linarith
  have hcop (a : Eisenstein) (ha : a ∈ fullSquarefreePrimeSupport R (W r) X e) : IsCoprime a d :=
    fullPrime_coprime_small_element (W r) X (fun i => zero_lt_one.trans_le (hX i))
      (hlo r) (hhi r) hrough' e d hd0 hdc ha
  have hTn : Tn ≤ L r := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hTc : Tc ≤ L r := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hn' := hn r X A d e u hd0 hTn hprod hrough hdη hAlo hA₂ he heN hu
  have hc' := hcube r X A e u hTc (hL r) hX hprod hrough' hAp hAhi
  have hcube' :
      ‖divisorCubePoissonContribution d (fullSquarefreePrimeSupport R (W r) X e)
          (fullPrimeCoefficient R (W r) X) u V A -
        (1/(norm d)^2:ℝ)*coprimeCubeMainTerm (fullSquarefreePrimeSupport R (W r) X e)
          (fullPrimeCoefficient R (W r) X) u V A‖ ≤
      Kc*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by
    rw [divisorCubePoissonContribution_eq hd hds _ (fun a ha => ⟨(hS a ha).1,hcop a ha⟩)
      _ _ _ hAp.le,← mul_sub,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (show 0 ≤ 1/(norm d)^2 by positivity)]
    apply (mul_le_of_le_one_left (_root_.norm_nonneg _) _).trans hc'
    simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1)
      (one_le_pow₀ hd1 : 1 ≤ (norm d)^2)
  rw [divisorCoprimeDispersionGram_split hd0 _ hS _ _ _ hV hV' hAp]
  calc
    _ = ‖(divisorCubePoissonContribution d (fullSquarefreePrimeSupport R (W r) X e)
          (fullPrimeCoefficient R (W r) X) u V A -
        (1/(norm d)^2:ℝ)*coprimeCubeMainTerm (fullSquarefreePrimeSupport R (W r) X e)
          (fullPrimeCoefficient R (W r) X) u V A) +
        divisorNoncubePoissonContribution d hd0 (fullSquarefreePrimeSupport R (W r) X e)
          (fullPrimeCoefficient R (W r) X) u V A‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans ((add_le_add hcube' hn').trans_eq (by ring))

end CubicFirstMoment

end

end OAI
