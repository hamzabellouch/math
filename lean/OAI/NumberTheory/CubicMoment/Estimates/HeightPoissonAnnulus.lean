import OAI.NumberTheory.CubicMoment.Estimates.HeightRadialForm
import OAI.NumberTheory.CubicMoment.Estimates.FinitePoissonRadial
import OAI.NumberTheory.CubicMoment.Estimates.HeightMeanSquare

namespace OAI

/-! The genuine finite Poisson contribution inherits the averaged
annular estimate with its exact geometric scalar A/(9L). -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma finitePoissonContribution_continuous_height (S H : Finset Eisenstein)
    (β : Eisenstein → ℂ) (V : ℝ → ℂ) (A : ℝ) :
    Continuous (fun u => finitePoissonContribution S H β u V A) := by
  unfold finitePoissonContribution
  apply continuous_finsetSum
  intro h hh
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  split_ifs
  · exact ((((continuous_const.mul (continuous_normTwist a)).mul
      (continuous_const.mul (continuous_normTwist b)).star).mul continuous_const).mul continuous_const)
  · exact continuous_const

theorem height_poisson_annulus_saving
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
      ∀ (r : γ) (X : ι → ℝ) (A B J : ℝ) (H : Finset Eisenstein)
        (e : Eisenstein) (u T : ℝ), L₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      0 < A → 1 ≤ B → B ≤ (L r)^(1+η) → 0 < J →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (∀ h ∈ H, J ≤ norm h ∧ norm h ≤ 2*J) →
      e ≠ 0 → norm e ≤ (L r)^σ → (1+Real.log (L r))^m ≤ T →
      T ≤ (L r)^(7/20:ℝ) → |u| ≤ (L r)^(7/20:ℝ) →
      (1+A*J/(27*(L r)^2))^q*dyadicHeightMean (fun t =>
        ‖finitePoissonContribution (fullSquarefreePrimeSupport R (W r) X e) H
          (fullPrimeCoefficient R (W r) X) (u+t) V A‖) T ≤
        K*A*L r*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hbound⟩ := height_radial_form_saving
    (γ := γ) (ι := ι) hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ V hV hV' k q
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K,L₀,m,hK,hbound⟩ := hbound L W hL hW hlo hhi
  refine ⟨K/9,L₀,m,by positivity,?_⟩
  intro r X A B J H e u T hL₀ hprod hX hA hB hBL hJ hH hHJ he heN hT hThi hu
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  let phase := fun h : Eisenstein =>
    (Real.fourierChar (tracePair (h:ℂ) (1/(3*traceLambda))):ℂ)
  have hb := hbound r X B J H e u T (A*J/(27*(L r)^2)) phase hL₀ hprod hX hB hBL hJ
    hH hHJ (fun h _ => by simp [phase]) he heN hT hThi hu (by positivity)
  have heq (t : ℝ) :
      ‖finitePoissonContribution (fullSquarefreePrimeSupport R (W r) X e) H
        (fullPrimeCoefficient R (W r) X) (u+t) V A‖ = (A/(9*L r))*
      ‖normCoprimeRadialForm (fullSquarefreePrimeSupport R (W r) X e) H
        (fun a => star (fullPrimeCoefficient R (W r) X a*mellinPhase (u+t) (norm a)))
        (fun a => star (fullPrimeCoefficient R (W r) X a*mellinPhase (u+t) (norm a)))
        phase (fun h => norm h/J) (fun a => norm a/L r) V (A*J/(27*(L r)^2))‖ := by
    rw [finitePoissonContribution_radial _ _
      (fun a ha => primary_ne_zero (fullSquarefreePrimeSupport_primary R (W r) X e ha).1)
      _ _ _ hA.le hLp hJ,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (show 0 ≤ A/(9*L r) by positivity)]
  simp_rw [heq]
  rw [dyadicHeightMean_const_mul]
  calc
    _ = (A/(9*L r))*((1+A*J/(27*(L r)^2))^q *
        dyadicHeightMean (fun t =>
          ‖normCoprimeRadialForm (fullSquarefreePrimeSupport R (W r) X e) H
            (fun a => star (fullPrimeCoefficient R (W r) X a*mellinPhase (u+t) (norm a)))
            (fun a => star (fullPrimeCoefficient R (W r) X a*mellinPhase (u+t) (norm a)))
            phase (fun h => norm h/J) (fun a => norm a/L r) V (A*J/(27*(L r)^2))‖) T) := by ring
    _ ≤ (A/(9*L r))*(K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp

end CubicFirstMoment

end

end OAI
