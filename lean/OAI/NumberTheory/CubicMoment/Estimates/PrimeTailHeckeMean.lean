import OAI.NumberTheory.CubicMoment.Estimates.PrimeTailMellinScale
import OAI.NumberTheory.CubicMoment.Estimates.GroupedPrimeHeight

namespace OAI

/-! The published Hecke height mean applied through the full original
product envelope. The bounded shift condition is discharged using eight
Mellin moments and the actual coarse prime-convolution bound. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem full_prime_product_smoothed_height
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (LA LB : γ → ℝ) (WA : γ → κ → ℝ → ℂ) (WB : γ → ι → ℝ → ℂ)
    (hLA : ∀ r, 1 ≤ LA r) (hLB : ∀ r, 1 ≤ LB r)
    (hWA : LogarithmicWeightFamily (fun z : γ × κ => LA z.1) (fun z => WA z.1 z.2))
    (hWB : LogarithmicWeightFamily (fun z : γ × ι => LB z.1) (fun z => WB z.1 z.2))
    (hAlo : ∀ r i x, x < 1 → WA r i x = 0)
    (hAhi : ∀ r i x, R < x → WA r i x = 0)
    (hBlo : ∀ r i x, x < 1 → WB r i x = 0)
    (hBhi : ∀ r i x, R < x → WB r i x = 0)
    (hWAone : ∀ r i x, ‖WA r i x‖ ≤ 1) (hWBone : ∀ r i x, ‖WB r i x‖ ≤ 1)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (k : ℕ) :
    ∃ (η : ℝ) (G : ℕ) (K B₀ : ℝ) (m : ℕ), 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (XA : κ → ℝ) (XB : ι → ℝ) (X T : ℝ),
      B₀ ≤ LB r → (∏ i, XA i) = LA r → (∏ i, XB i) = LB r →
      (∀ i, 1 ≤ XA i) → (∀ i, (2*LB r)^c < XB i) →
      (LB r)^(1-η/4) ≤ LA r → LA r ≤ (LB r)^2/(1+Real.log (LB r))^G →
      0 < X →
      (1+Real.log (LB r))^m ≤ T → T ≤ (LB r)^(7/20:ℝ) →
      dyadicHeightMean (fun t => ‖productGaussSmoothed
        (fullSquarefreePrimeSupport R (WA r) XA 1)
        (fullSquarefreePrimeSupport R (WB r) XB 1)
        (fullPrimeCoefficient R (WA r) XA) (fullPrimeCoefficient R (WB r) XB)
        0 W X t‖) T ≤
        K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k := by
  obtain ⟨η,σ,G,K,B₀,m,hη,hηone,hσ,hK,hmean⟩ := full_prime_product_height_bilinear
    hpub hHuxley hperiod hMV hC hc hc1 hR hGI hGQ LA LB WA WB hLA hLB hWA hWB
    hAlo hAhi hBlo hBhi k
  obtain ⟨B₁,hB₁⟩ := eventually_atTop.mp
    (overlap_power_log_saving (by norm_num : (0:ℝ) < 1) k 0)
  let M := primeCoefficientMassConstant R (Fintype.card κ)*
    primeCoefficientMassConstant R (Fintype.card ι)
  have hM : 0 ≤ M := by dsimp [M,primeCoefficientMassConstant]; positivity
  let K' := K*zeroLineMellinMass W+2*M*zeroLineMellinMoment W 8+1
  have hmass := zeroLineMellinMass_nonneg W
  have hmom := zeroLineMellinMoment_nonneg W 8
  refine ⟨η,G,K',max B₀ B₁,m,hη,hηone,by dsimp [K']; positivity,?_⟩
  intro r XA XB X T hB hprodA hprodB hXA hXB hAlow hAhigh hX hT hThi
  have hAp : 0 < LA r := zero_lt_one.trans_le (hLA r)
  have hBp : 0 < LB r := zero_lt_one.trans_le (hLB r)
  have hL : 0 < 1+Real.log (LB r) := by linarith [Real.log_nonneg (hLB r)]
  have hLone : 1 ≤ 1+Real.log (LB r) := by linarith [Real.log_nonneg (hLB r)]
  have hAB : LA r ≤ (LB r)^2 :=
    hAhigh.trans (div_le_self (sq_nonneg _) (one_le_pow₀ hLone))
  have hTpos : 0 < T := (pow_pos hL m).trans_le hT
  have hsmall (u : ℝ) (hu : |u| ≤ (LB r)^(1/4:ℝ)) :
      dyadicHeightMean (fun t => ‖fullPrimeProductGauss R (WA r) (WB r) XA XB (u+t)‖) T ≤
        K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k := by
    exact hmean r XA XB 1 1 u T ((le_max_left _ _).trans hB) hprodA hprodB hXA hXB
      hAlow hAhigh one_ne_zero (by simp; exact Real.one_le_rpow (hLB r) hσ.le) hT hThi
      (hu.trans (Real.rpow_le_rpow_of_exponent_le (hLB r) (by norm_num)))
  have hb := fullPrimeProductSmoothed_height_mean (zero_le_one.trans hR) (WA r) (WB r) XA XB
    (fun i => zero_lt_one.trans_le (hXA i))
    (fun i => lt_trans (Real.rpow_pos_of_pos (by linarith [hLB r] : 0 < 2*LB r) c) (hXB i))
    (hAlo r) (hAhi r) (hBlo r) (hBhi r) (hWAone r) (hWBone r)
    W hW hpos hsm hX (by positivity) (Real.rpow_pos_of_pos hBp _) hTpos 8 hsmall
  rw [hprodA,hprodB] at hb
  have hlog : (1+Real.log (LB r))^k ≤ LB r := by
    have hh := hB₁ (LB r) ((le_max_right _ _).trans hB)
    simp only [Real.rpow_one,Nat.mul_zero,pow_zero,div_one] at hh
    exact (div_le_one hBp).mp hh
  have he := primeTail_mellin_error_scale hAp (hLB r) hAB
  have he' : LA r*LB r/((LB r)^(1/4:ℝ))^8 ≤
      (LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k :=
    he.trans (div_le_div_of_nonneg_left (by positivity) (pow_pos hL k) hlog)
  have herr : (2*(M*LA r*LB r))/((LB r)^(1/4:ℝ))^8*zeroLineMellinMoment W 8 ≤
      (2*M*zeroLineMellinMoment W 8)*
        ((LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k) := by
    calc
      _ = (2*M*zeroLineMellinMoment W 8)*
          (LA r*LB r/((LB r)^(1/4:ℝ))^8) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he' (by positivity)
  apply hb.trans
  change (K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k)*zeroLineMellinMass W+
    (2*(M*LA r*LB r))/((LB r)^(1/4:ℝ))^8*zeroLineMellinMoment W 8 ≤ _
  calc
    _ ≤ (K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k)*zeroLineMellinMass W+
        (2*M*zeroLineMellinMoment W 8)*
          ((LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k) :=
      add_le_add le_rfl herr
    _ = (K*zeroLineMellinMass W+2*M*zeroLineMellinMoment W 8)*
        ((LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k) := by ring
    _ ≤ K'*((LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k) :=
      mul_le_mul_of_nonneg_right (by dsimp [K']; linarith) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
