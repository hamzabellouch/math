import OAI.NumberTheory.CubicMoment.Estimates.NoncubeRadialForm
import OAI.NumberTheory.CubicMoment.Estimates.FinitePoissonRadial

namespace OAI

/-! The actual finite Poisson contribution on a noncube annulus, with
the geometric factor A/L and arbitrary decay in A J/L². -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem noncube_poisson_annulus_saving (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k U q : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A B J : ℝ)
      (H : Finset Eisenstein) (e : Eisenstein) (u : ℝ), T₀ ≤ L r →
      (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) →
      0 < A → 1 ≤ B → B ≤ (L r)^(1+η) → 0 < J →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ z : Eisenstein, z^3 = h) →
      (∀ h ∈ H, J ≤ norm h ∧ norm h ≤ 2*J) →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U →
      (1+A*J/(27*(L r)^2))^q *
        ‖finitePoissonContribution (fullSquarefreePrimeSupport R (W r) X e) H
          (fullPrimeCoefficient R (W r) X) u V A‖ ≤
        K*A*L r*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  obtain ⟨η,σ,hη,hη₁,hσ,hbound⟩ := noncube_radial_form_saving
    (γ := γ) (ι := ι) hSW hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ V hV hV' k U q
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K,T₀,hK,hbound⟩ := hbound L W hL hW hlo hhi
  refine ⟨K/9,T₀,by positivity,?_⟩
  intro r X A B J H e u hT hprod hX hA hB hBL hJ hH hHJ he heN hu
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  let phase := fun h : Eisenstein =>
    (Real.fourierChar (tracePair (h:ℂ) (1/(3*traceLambda))):ℂ)
  have hb := hbound r X B J H e u (A*J/(27*(L r)^2)) phase hT hprod hX hB hBL hJ
    hH hHJ (fun h _ => by simp [phase]) he heN hu (by positivity)
  rw [finitePoissonContribution_radial _ _
    (fun a ha => primary_ne_zero (fullSquarefreePrimeSupport_primary R (W r) X e ha).1)
    _ _ _ hA.le hLp hJ,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (show 0 ≤ A/(9*L r) by positivity)]
  calc
    _ = (A/(9*L r))*((1+A*J/(27*(L r)^2))^q *
        ‖normCoprimeRadialForm (fullSquarefreePrimeSupport R (W r) X e) H
          (fun a => star (fullPrimeCoefficient R (W r) X a*mellinPhase u (norm a)))
          (fun a => star (fullPrimeCoefficient R (W r) X a*mellinPhase u (norm a)))
          phase (fun h => norm h/J) (fun a => norm a/L r) V (A*J/(27*(L r)^2))‖) := by ring
    _ ≤ (A/(9*L r))*(K*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp

end CubicFirstMoment

end

end OAI
