import OAI.NumberTheory.CubicMoment.Estimates.TripleTransitionCentered
import OAI.NumberTheory.CubicMoment.Estimates.TripleTransitionHeight
import OAI.NumberTheory.CubicMoment.Decomposition.PrimeProductCenteredTail
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeLowWindow

namespace OAI

/-! Full Mellin transfer of the exceptional triple transition estimate.
The complementary integral is retained and bounded using the genuine
height mean through B^(7/20), then rapid transform decay. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem two_prime_transition_smoothed {γ ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 2) (hpnt : PrimaryPrimePNT)
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C c : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hc : 0 < c)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : UniformLogWeights W) (hlo : ∀ r x, x < 1 → W r x = 0)
    (hhi : ∀ r x, 2 < x → W r x = 0) (hW1 : ∀ r x, ‖W r x‖ ≤ 1) (U : ℕ) :
    ∃ η K T₀ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (A X u : ℝ) (WA : ι → ℝ → ℂ) (XA : ι → ℝ),
      T₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 → 0 < X →
      |u| ≤ (1+Real.log (L r))^U →
      (∏ i, XA i) = A → (∀ i, (L r)^c ≤ XA i) →
      (∀ i x, x < 1 → WA i x = 0) → (∀ i x, 2 < x → WA i x = 0) →
      (∀ i x, ‖WA i x‖ ≤ 1) →
      ‖centeredProductSmoothed (fullSquarefreePrimeSupport 2 WA XA 1)
        (fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1)
        (fullPrimeCoefficient 2 WA XA)
        (fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r))
        0 primeProductEnvelope X u‖ ≤
        K*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^(3/2:ℝ) := by
  obtain ⟨ηh,Kh,Th,m,hηh,hηh1,hKh,hheight⟩ := two_prime_transition_height hcard
    hpub hHuxley hperiod hMV hC hGI hGQ L W hL hW hlo hhi hW1
  obtain ⟨ηp,Kp,Tp,hηp,hηp1,hKp,hpoint⟩ := two_prime_transition_centered hcard hpnt
    hSW hpub hHuxley hperiod hMV hC hc hGI hGQ L W hL hW hlo hhi hW1 (U+(m+2)+2)
  obtain ⟨D,hD,htail⟩ := fullPrimeProduct_centered_mellin_tail (ι := Unit) (κ := ι)
    (by norm_num : (0:ℝ) ≤ 2) primeProductEnvelope primeProductEnvelope_compact
    primeProductEnvelope_positive primeProductEnvelope_smooth
  let M := zeroLineMellinMass primeProductEnvelope
  have hM : 0 ≤ M := by
    rw [show M = ∫ t : ℝ, ‖zeroLineMellinWeight primeProductEnvelope 1 t‖ from
      (zeroLineMellinWeight_mass primeProductEnvelope (by norm_num)).symm]
    exact integral_nonneg (fun _ => _root_.norm_nonneg _)
  obtain ⟨Tg,hTg⟩ := eventually_atTop.mp
    (overlap_power_log_saving (by norm_num : (0:ℝ) < 7/20) U 0)
  refine ⟨min ηp ηh,M*Kp+D*(Kh+1),max (max Tp Th) (max Tg (Real.exp 1)),
    lt_min hηp hηh,(min_le_left _ _).trans hηp1,by positivity,?_⟩
  intro r A X u WA XA hT hrough hAlo hAhi hX hu hprod hXA hAlow hAhigh hWA
  have hTp : Tp ≤ L r := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hTh : Th ≤ L r := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have hTg' : Tg ≤ L r := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hB : 0 < L r := zero_lt_one.trans_le (hL r)
  have hA : 0 < A := (Real.rpow_pos_of_pos hB _).trans_le hAlo
  have hlog : 1 ≤ Real.log (L r) := by
    have hh := Real.log_le_log (Real.exp_pos 1)
      ((le_max_right Tg (Real.exp 1)).trans ((le_max_right _ _).trans hT))
    simpa only [Real.log_exp] using hh
  have hz : 0 < 1+Real.log (L r) := by linarith
  have hz1 : 1 ≤ 1+Real.log (L r) := by linarith
  have hXi : ∀ i, 0 < XA i := fun i => (Real.rpow_pos_of_pos hB c).trans_le (hXA i)
  have hAp : (L r)^(1-ηp/4) ≤ A :=
    (Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith [min_le_left ηp ηh])).trans hAlo
  have hAh : (L r)^(1-ηh/4) ≤ A :=
    (Real.rpow_le_rpow_of_exponent_le (hL r) (by linarith [min_le_right ηp ηh])).trans hAlo
  let S := (1+Real.log (L r))^(m+2)
  have hS : 0 < S := pow_pos hz _
  have huB : |u| ≤ (L r)^(7/20:ℝ) := by
    apply hu.trans
    apply (div_le_one (Real.rpow_pos_of_pos hB _)).mp
    simpa only [Nat.mul_zero,pow_zero,div_one] using hTg (L r) hTg'
  have htail' := htail WA (fun _ : Unit => W r) XA (fun _ => L r) hXi (fun _ => hB)
    hAlow hAhigh (fun _ => hlo r) (fun _ => hhi r) hWA (fun _ => hW1 r)
    (by simpa only [Fintype.prod_unique] using hL r)
    (by simpa only [Fintype.prod_unique,hprod] using hAhi) X u S Kh hX hS hKh.le (by
      intro T hST hThi
      have hh := hheight r A u T WA XA hTh hrough hAh hAhi
        ((pow_le_pow_right₀ hz1 (Nat.le_add_right m 2)).trans hST)
        (by simpa only [Fintype.prod_unique] using hThi) huB hprod hXi hAlow hAhigh hWA
      simpa only [Fintype.prod_unique,hprod,Real.mul_rpow hA.le hB.le,mul_assoc] using hh)
  have hlocal := centeredMellinWindow_bound (fullSquarefreePrimeSupport 2 WA XA 1)
    (fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1)
    (fullPrimeCoefficient 2 WA XA) (fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r))
    0 primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth hX
    (by positivity : 0 ≤ Kp*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^(3/2:ℝ)) S u (by
      intro τ hτ
      exact hpoint r A (u-τ) WA XA hTp hrough hAp hAhi
        (semiprime_low_mellin_height (by linarith) U (m+2)
          ⟨by nlinarith [neg_abs_le u,pow_nonneg hz.le U],
            by nlinarith [le_abs_self u,pow_nonneg hz.le U]⟩ hτ)
        hprod hXA hAlow hAhigh hWA)
  have he := centered_product_mellin_complement (fullSquarefreePrimeSupport 2 WA XA 1)
    (fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1)
    (fullPrimeCoefficient 2 WA XA) (fullPrimeCoefficient 2 (fun _ : Unit => W r) (fun _ => L r))
    (fun p hp => (fullSquarefreePrimeSupport_primary _ _ _ _ hp).1)
    (fun p hp => (fullSquarefreePrimeSupport_primary _ _ _ _ hp).1)
    0 primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth hX S u
  have hdenom : (1+Real.log (L r))^(3/2:ℝ) ≤ S := by
    dsimp [S]
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hz1 (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) m])
  have ht : D*(Kh+1)*((∏ i, XA i)*(∏ _i : Unit, L r))^(5/6:ℝ)/S ≤
      D*(Kh+1)*A^(5/6:ℝ)*(L r)^(5/6:ℝ)/(1+Real.log (L r))^(3/2:ℝ) := by
    rw [hprod,Fintype.prod_unique,Real.mul_rpow hA.le hB.le]
    exact (div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hz _) hdenom).trans_eq (by ring)
  rw [he]
  apply (norm_add_le _ _).trans
  exact (add_le_add hlocal (htail'.trans ht)).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
