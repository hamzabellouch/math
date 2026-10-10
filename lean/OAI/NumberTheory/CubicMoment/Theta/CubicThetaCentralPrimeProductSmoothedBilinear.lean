import OAI.NumberTheory.CubicMoment.Decomposition.PrimeProductSmoothedBilinear
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralPrimeProductBilinear

namespace OAI

/-! Full Mellin transfer of the published-input prime-product estimate.
Both the finite window and its complete complement are controlled, with
constants uniform in the independent weights, scales and envelope length. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype κ] [DecidableEq κ]


theorem full_prime_centered_smoothed_bilinear_actual
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (LA LB : γ → ℝ) (WA : γ → κ → ℝ → ℂ) (WB : γ → ι → ℝ → ℂ)
    (hLA : ∀ r, 1 ≤ LA r) (hLB : ∀ r, 1 ≤ LB r)
    (hWA : LogarithmicWeightFamily (fun z : γ × κ => LA z.1) (fun z => WA z.1 z.2))
    (hWB : LogarithmicWeightFamily (fun z : γ × ι => LB z.1) (fun z => WB z.1 z.2))
    (hAlo : ∀ r i x, x < 1 → WA r i x = 0) (hAhi : ∀ r i x, R < x → WA r i x = 0)
    (hBlo : ∀ r i x, x < 1 → WB r i x = 0) (hBhi : ∀ r i x, R < x → WB r i x = 0)
    (hWA1 : ∀ r i x, ‖WA r i x‖ ≤ 1) (hWB1 : ∀ r i x, ‖WB r i x‖ ≤ 1) (k U : ℕ) :
    ∃ (η : ℝ) (G : ℕ) (K B₀ : ℝ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (XA : κ → ℝ) (XB : ι → ℝ) (X u : ℝ),
      B₀ ≤ LB r → (∏ i, XA i) = LA r → (∏ i, XB i) = LB r →
      (∀ i, 1 ≤ XA i) → (∀ i, (2*LB r)^c < XB i) →
      (LB r)^(1-η/16) ≤ LA r → LA r ≤ (LB r)^2/(1+Real.log (LB r))^G →
      0 < X → |u| ≤ (1+Real.log (LB r))^U →
      ‖centeredProductSmoothed (fullSquarefreePrimeSupport R (WA r) XA 1)
        (fullSquarefreePrimeSupport R (WB r) XB 1)
        (fullPrimeCoefficient R (WA r) XA) (fullPrimeCoefficient R (WB r) XB)
        0 primeProductEnvelope X u‖ ≤ K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k := by
  obtain ⟨ηh,σh,Gh,Kh,Th,m,hηh,hηh1,hσh,hKh,hheight⟩ := full_prime_product_height_bilinear
    hpub hHuxley hperiod hMV hC hc hc1 hR hGI hGQ LA LB WA WB hLA hLB hWA hWB
    hAlo hAhi hBlo hBhi 0
  obtain ⟨ηp,σp,Gp,Kp,Tp,hηp,hηp1,hσp,hKp,hpoint⟩ := full_prime_centered_product_bilinear_actual
    hSW hpub hHuxley hperiod hMV hC hc hc1 hR hGI hGQ  hGamma
    LA LB WA WB hLA hLB hWA hWB hAlo hAhi hBlo hBhi k (U+(m+k)+2)
  obtain ⟨D,hD,htail⟩ := fullPrimeProduct_centered_mellin_tail (ι := ι) (κ := κ)
    (zero_le_one.trans hR) primeProductEnvelope primeProductEnvelope_compact
    primeProductEnvelope_positive primeProductEnvelope_smooth
  let M := zeroLineMellinMass primeProductEnvelope
  have hM : 0 ≤ M := by
    rw [show M = ∫ t : ℝ, ‖zeroLineMellinWeight primeProductEnvelope 1 t‖ from
      (zeroLineMellinWeight_mass primeProductEnvelope (by norm_num)).symm]
    exact integral_nonneg (fun _ => _root_.norm_nonneg _)
  obtain ⟨Tg,hTg⟩ := eventually_atTop.mp
    (overlap_power_log_saving (by norm_num : (0:ℝ) < 7/20) U 0)
  refine ⟨min ηp ηh,max Gp Gh,M*Kp+D*(Kh+1),max (max Tp Th) (max Tg (Real.exp 1)),
    lt_min hηp hηh,(min_le_left _ _).trans hηp1,by positivity,?_⟩
  intro r XA XB X u hT hprodA hprodB hXA hXB hAlow hAhigh hX hu
  have hTp : Tp ≤ LB r := (le_max_left Tp Th).trans ((le_max_left _ _).trans hT)
  have hTh : Th ≤ LB r := (le_max_right Tp Th).trans ((le_max_left _ _).trans hT)
  have hTg' : Tg ≤ LB r := (le_max_left Tg (Real.exp 1)).trans ((le_max_right _ _).trans hT)
  have hB1 := hLB r
  have hBp : 0 < LB r := zero_lt_one.trans_le hB1
  have hAp : 0 < LA r := zero_lt_one.trans_le (hLA r)
  have hlog : 1 ≤ Real.log (LB r) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      ((le_max_right Tg (Real.exp 1)).trans ((le_max_right _ _).trans hT))
    simpa only [Real.log_exp] using h
  have hL : 0 < 1+Real.log (LB r) := by linarith
  have hL1 : 1 ≤ 1+Real.log (LB r) := by linarith
  have hXA' : ∀ i, 0 < XA i := fun i => zero_lt_one.trans_le (hXA i)
  have hXB' : ∀ i, 0 < XB i := fun i =>
    (Real.rpow_pos_of_pos (by positivity : 0 < 2*LB r) c).trans (hXB i)
  have hupper (g : ℕ) (hg : g ≤ max Gp Gh) : LA r ≤ (LB r)^2/(1+Real.log (LB r))^g :=
    hAhigh.trans (div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hL g)
      (pow_le_pow_right₀ hL1 hg))
  have hAraw : LA r ≤ (LB r)^2 :=
    (hupper 0 (Nat.zero_le _)).trans_eq (by simp)
  have hApoint : (LB r)^(1-ηp/16) ≤ LA r :=
    (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith [min_le_left ηp ηh])).trans hAlow
  have hAheight : (LB r)^(1-ηh/4) ≤ LA r :=
    (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith [min_le_right ηp ηh])).trans hAlow
  let S := (1+Real.log (LB r))^(m+k)
  have hS : 0 < S := pow_pos hL _
  have huB : |u| ≤ (LB r)^(7/20:ℝ) := by
    apply hu.trans
    apply (div_le_one (Real.rpow_pos_of_pos hBp _)).mp
    simpa only [Nat.mul_zero,pow_zero,div_one] using hTg (LB r) hTg'
  have htail' := htail (WA r) (WB r) XA XB hXA' hXB' (hAlo r) (hAhi r) (hBlo r) (hBhi r)
    (hWA1 r) (hWB1 r) (by simpa only [hprodB] using hB1)
    (by simpa only [hprodA,hprodB] using hAraw) X u S Kh hX hS hKh.le (by
      intro T hST hThi
      have hh := hheight r XA XB 1 1 u T hTh hprodA hprodB hXA hXB hAheight
        (hupper Gh (le_max_right _ _)) one_ne_zero
        (by rw [norm_one_eq]; exact Real.one_le_rpow hB1 hσh.le)
        ((pow_le_pow_right₀ hL1 (Nat.le_add_right m k)).trans hST)
        (by simpa only [hprodB] using hThi) huB
      simpa only [pow_zero,div_one,fullPrimeProductGauss,hprodA,hprodB,
        Real.mul_rpow hAp.le hBp.le,mul_assoc] using hh)
  have hlocal := centeredMellinWindow_bound (fullSquarefreePrimeSupport R (WA r) XA 1)
    (fullSquarefreePrimeSupport R (WB r) XB 1) (fullPrimeCoefficient R (WA r) XA)
    (fullPrimeCoefficient R (WB r) XB) 0 primeProductEnvelope primeProductEnvelope_compact
    primeProductEnvelope_positive primeProductEnvelope_smooth hX
    (by positivity : 0 ≤ Kp*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k) S u (by
      intro τ hτ
      have hh := hpoint r XA XB 1 1 (u-τ) hTp hprodA hprodB hXA hXB hApoint
        (hupper Gp (le_max_left _ _)) one_ne_zero
        (by rw [norm_one_eq]; exact Real.one_le_rpow hB1 hσp.le)
        (semiprime_low_mellin_height (by linarith) U (m+k)
          (show u ∈ Icc (-(4/3)*(1+Real.log (LB r))^U)
              ((4/3)*(1+Real.log (LB r))^U) from
            ⟨by nlinarith [neg_abs_le u, pow_nonneg hL.le U],
              by nlinarith [le_abs_self u, pow_nonneg hL.le U]⟩) hτ)
      simpa only [centeredProductPolynomial,theta_zero,mul_one] using hh)
  have he := centered_product_mellin_complement (fullSquarefreePrimeSupport R (WA r) XA 1)
    (fullSquarefreePrimeSupport R (WB r) XB 1) (fullPrimeCoefficient R (WA r) XA)
    (fullPrimeCoefficient R (WB r) XB)
    (fun p hp => (fullSquarefreePrimeSupport_primary _ _ _ _ hp).1)
    (fun p hp => (fullSquarefreePrimeSupport_primary _ _ _ _ hp).1)
    0 primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth hX S u
  have ht : D*(Kh+1)*((∏ i, XA i)*(∏ i, XB i))^(5/6:ℝ)/S ≤
      D*(Kh+1)*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k := by
    rw [hprodA,hprodB,Real.mul_rpow hAp.le hBp.le]
    exact (div_le_div_of_nonneg_left (by positivity) (pow_pos hL k)
      (pow_le_pow_right₀ hL1 (Nat.le_add_left k m))).trans_eq (by ring)
  rw [he]
  apply (norm_add_le _ _).trans
  exact (add_le_add hlocal (htail'.trans ht)).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
