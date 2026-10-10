import OAI.NumberTheory.CubicMoment.Angular.AngularPrimeProductCentered
import OAI.NumberTheory.CubicMoment.Angular.AngularTripleTransitionBilinear
import OAI.NumberTheory.CubicMoment.Angular.AngularPrimeProductModelMass

namespace OAI

/-! The actual two-prime/one-prime centered polynomial at the transition.
Both coefficient masses are derived from prime counting. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_two_prime_transition_centered {γ ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 2) (hpnt : PrimaryPrimePNT)
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C c : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hc : 0 < c)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : UniformLogWeights W) (hlo : ∀ r x, x < 1 → W r x = 0)
    (hhi : ∀ r x, 2 < x → W r x = 0) (hW1 : ∀ r x, ‖W r x‖ ≤ 1) (U : ℕ) :
    ∃ η K T₀ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (A u : ℝ) (WA : ι → ℝ → ℂ) (XA : ι → ℝ),
      T₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 → |u| ≤ (1+Real.log (L r))^U →
      (∏ i, XA i) = A → (∀ i, (L r)^c ≤ XA i) →
      (∀ i x, x < 1 → WA i x = 0) → (∀ i x, 2 < x → WA i x = 0) →
      (∀ i x, ‖WA i x‖ ≤ 1) →
      ‖centeredProductPolynomial (fullSquarefreePrimeSupport 2 WA XA 1)
        (fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1)
        (fullPrimeCoefficient 2 WA XA)
        (fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r)) ℓ u‖ ≤
        K*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^(3/2:ℝ) := by
  obtain ⟨η,Kg,Tg,hη,hη1,hKg,hgauss⟩ := angular_two_prime_transition_bilinear ℓ hcard hpnt
    hSW hℓ hpub hHuxley hperiod hMV hC hc hGI hGQ L W hL hW hlo hhi hW1 U
  obtain ⟨MA,hMA,hmA⟩ := fullPrimeCoefficient_power_scale_moments (ι := ι) hpnt
    (R := 2) (by norm_num) hc
  obtain ⟨TA,hmA⟩ := eventually_atTop.mp hmA
  obtain ⟨MB,hMB,hmB⟩ := fullPrimeCoefficient_power_scale_moments (ι := Unit) hpnt
    (R := 2) (by norm_num) (by norm_num : (0:ℝ) < 1)
  obtain ⟨TB,hmB⟩ := eventually_atTop.mp hmB
  let Km := MA*MB*cStar
  have hKm : 0 < Km := mul_pos (mul_pos hMA hMB) cStar_pos
  refine ⟨η,Kg+Km,max Tg (max TA TB),hη,hη1,by positivity,?_⟩
  intro r A u WA XA hT hrough hAlo hAhi hu hprod hXA hAlow hAhigh hWA
  have hB : 0 < L r := zero_lt_one.trans_le (hL r)
  have hA : 0 < A := (Real.rpow_pos_of_pos hB _).trans_le hAlo
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hXi (i : ι) : 0 < XA i := (Real.rpow_pos_of_pos hB c).trans_le (hXA i)
  have hma := (hmA (L r) ((le_max_left _ _).trans ((le_max_right _ _).trans hT))
    WA XA hXA hWA 1).1
  rw [hprod,hcard] at hma
  have hmb := (hmB (L r) ((le_max_right _ _).trans ((le_max_right _ _).trans hT))
    (fun _ : Unit => W r) (fun _ => L r) (by intro _; rw [Real.rpow_one])
    (fun _ => hW1 r) 1).1
  simp only [Fintype.card_unique,Fintype.prod_unique,pow_one] at hmb
  have hm := fullAngularPrimeProductModel_density_bound ℓ hA hB hz hMA.le hMB.le WA
    (fun _ : Unit => W r) XA (fun _ => L r) hXi (fun _ => hB) hprod (by simp)
    hAlow hAhigh (fun _ => hlo r) (fun _ => hhi r) hma hmb u
  have hg := hgauss r A u WA XA ((le_max_left _ _).trans hT) hrough hAlo hAhi hu
    hprod hXA hAlow hAhigh hWA
  have hgAngular : ‖fullAngularPrimeProductGauss ℓ 2 WA (fun _ : Unit => W r) XA (fun _ => L r) u‖ ≤
      Kg*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^(3/2:ℝ) := by
    simpa only [fullAngularPrimeProductGauss, productGaussPolynomial, angularHeightPrimeCoefficient, theta_mul, mul_assoc, mul_left_comm, mul_comm] using hg
  have hdenom : (1+Real.log (L r))^(3/2:ℝ) ≤ (1+Real.log (L r))^3 := by
    rw [← Real.rpow_natCast (1+Real.log (L r)) 3]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.log_nonneg (hL r)]) (by norm_num)
  have hm' : ‖fullAngularPrimeProductModel ℓ 2 WA (fun _ : Unit => W r) XA (fun _ => L r) u‖ ≤
      Km*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^(3/2:ℝ) :=
    hm.trans (div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hz _) hdenom)
  rw [fullAngularPrimeProduct_centered]
  apply (norm_sub_le _ _).trans
  exact (add_le_add hgAngular hm').trans_eq (by ring)

end CubicFirstMoment

end

end OAI
