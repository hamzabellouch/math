import OAI.NumberTheory.CubicMoment.Estimates.PrimeTailHeckeMean
import OAI.NumberTheory.CubicMoment.Estimates.PrimeTailWindow
import OAI.NumberTheory.CubicMoment.Estimates.BilinearHeightTail
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedTailEnvelope

namespace OAI

/-! The full-envelope Hecke mean summed over the actual finite height tail. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem full_prime_product_envelope_tail
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
      ∀ (r : γ) (XA : κ → ℝ) (XB : ι → ℝ) (X H T : ℝ),
      B₀ ≤ LB r → (∏ i, XA i) = LA r → (∏ i, XB i) = LB r →
      (∀ i, 1 ≤ XA i) → (∀ i, (2*LB r)^c < XB i) →
      (LB r)^(1-η/4) ≤ LA r → LA r ≤ (LB r)^2/(1+Real.log (LB r))^G →
      0 < X →
      (1+Real.log (LB r))^m ≤ T → 1 ≤ H → H ≤ (LB r)^3 →
      2*Real.pi*H ≤ (LB r)^(7/20:ℝ) →
      ‖envelopeCutoffBilinearTail
        (fullSquarefreePrimeSupport R (WA r) XA 1)
        (fullSquarefreePrimeSupport R (WB r) XB 1)
        (fullPrimeCoefficient R (WA r) XA) (fullPrimeCoefficient R (WB r) XB)
        W H T X‖ ≤
        K*(LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)/(1+Real.log (LB r))^k := by
  obtain ⟨η,G,K,B₀,m,hη,hηone,hK,hmean⟩ := full_prime_product_smoothed_height
    hpub hHuxley hperiod hMV hC hc hc1 hR hGI hGQ LA LB WA WB hLA hLB hWA hWB
    hAlo hAhi hBlo hBhi hWAone hWBone W hW hpos hsm (k+1)
  obtain ⟨K₀,hK₀,hsum⟩ := height_window_sum_log_saving
  refine ⟨η,G,K₀*(2*K),B₀,m,hη,hηone,by positivity,?_⟩
  intro r XA XB X H T hB hprodA hprodB hXA hXB hAlow hAhigh hX hT hH hHB hHtop
  let P := fullSquarefreePrimeSupport R (WA r) XA 1
  let S := fullSquarefreePrimeSupport R (WB r) XB 1
  let α := fullPrimeCoefficient R (WA r) XA
  let β := fullPrimeCoefficient R (WB r) XB
  have hL1 : 1 ≤ 1+Real.log (LB r) := by linarith [Real.log_nonneg (hLB r)]
  have hAp : 0 < LA r := zero_lt_one.trans_le (hLA r)
  have hBp : 0 < LB r := zero_lt_one.trans_le (hLB r)
  have hT1 : 1 ≤ T := (one_le_pow₀ hL1).trans hT
  have hb (u : ℝ) (htu : T ≤ u) (huh : u < 2*Real.pi*H) :
      ‖productGaussWindow P S α β 0 W H u X‖ ≤
        (2*K)*((LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ))/(1+Real.log (LB r))^(k+1) := by
    have hu : 0 < u := zero_lt_one.trans_le (hT1.trans htu)
    apply (productGaussWindow_bound P S α β 0 W (zero_lt_one.trans_le hH) hu X).trans
    have hm := hmean r XA XB X u hB hprodA hprodB hXA hXB hAlow hAhigh hX
      (hT.trans htu) (huh.le.trans hHtop)
    exact (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)
  have hs := hsum H T (LB r) ((LA r)^(5/6:ℝ)*(LB r)^(5/6:ℝ)) (2*K) k
    (fun u => productGaussWindow P S α β 0 W H u X) hH hT1 (hLB r) hHB
    (by positivity) (by positivity) hb
  have he : envelopeCutoffBilinearTail P S α β W H T X =
      ∑ v ∈ Finset.range (heightWindowCount H T),
        productGaussWindow P S α β 0 W H (T*(3/2:ℝ)^v) X := by
    unfold envelopeCutoffBilinearTail productGaussWindow
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [productGaussHeightWindowKernel,theta_zero,one_mul]
    ring
  change ‖envelopeCutoffBilinearTail P S α β W H T X‖ ≤ _
  rw [he]
  exact hs.trans_eq (by ring)

end CubicFirstMoment

end

end OAI
