import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeLowGroup
import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeHeckeWindow
import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeOrdinaryGroup
import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeHeightRanges
import OAI.NumberTheory.CubicMoment.Estimates.PrimeBoxRange
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailHeightPrefix

namespace OAI

/-! The ordinary-height prefix on an actual group. Small groups use the
logarithmic localization bound on two aligned full tails. Larger groups
use the published Hecke estimate on each retained window. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem tailPrime_ordinary_group_prefix {i j : ℕ} (s : Finset (Fin i ⊕ Fin j))
    (hpnt : PrimaryPrimePNT) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (n : ℕ) :
    ∃ (Ct : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (z : largeTupleBoxIndex i j) (H T : ℝ), z.1.1 = X →
      let B := largeTupleGroupLength s z
      let A := largeTupleGroupLength (Finset.univ\s) z
      ((1/2:ℝ)^(1/3:ℝ)/2^(i+j))*X^(1/3:ℝ) ≤ B → B^2 ≤ 3*X →
      X/(2*2^(i+j)) ≤ A*B → A*B ≤ 3*X →
      (∀ a : s, (2*B)^(ξ/2) < largeTupleNormScale z.1.2 a) →
      (1+Real.log X)^Ct ≤ T → 1 ≤ H → H ≤ X^(1/6+1/3000:ℝ) →
      ‖∑ v ∈ Finset.range (heightWindowCount H T),
        if T*(3/2:ℝ)^v ≤ X^(1/100:ℝ) then
          productGaussWindow (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
            (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
            (largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s)
            (largeTupleOtherCoefficient ξ z.1.1 z.1.2 s)
            0 primeProductEnvelope H (T*(3/2:ℝ)^v) z.1.1 else 0‖ ≤
        K*X^(5/6:ℝ)/(1+Real.log X)^n := by
  obtain ⟨K₁,m₁,hK₁,hb₁⟩ := tailPrime_low_group s hHuxley hMV hC hpnt n 1
  obtain ⟨η,G,K₂,B₂,m₂,hη,_hηone,hK₂,hb₂⟩ :=
    tailPrime_hecke_window s hpub hHuxley hperiod hMV hC hξ hξz hGI hGQ (n+1)
  obtain ⟨D₀,hD₀,hcount⟩ := heightWindowCount_log_bound
  let c : ℝ := (1/2:ℝ)^(1/3:ℝ)/2^(i+j)
  let D : ℝ := 2*2^(i+j)
  let W : ℝ := 2*(2:ℝ)^s.card
  let Q : ℝ := (2:ℝ)^(Fintype.card {x : Fin i ⊕ Fin j // x ∉ s})
  have hc : 0 < c := by dsimp [c]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hW : 1 ≤ W := by dsimp [W]; have := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := s.card); linarith
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let Ct := max (m₁+1) (m₂+1)
  let L₁ := K₁*3^(5/6:ℝ)/(1/4:ℝ)^n
  let L₂ := K₂*3^(5/6:ℝ)/(1/4:ℝ)^(n+1)
  refine ⟨Ct,2*L₁+D₀*L₂,by dsimp [L₁,L₂]; positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (Real.tendsto_log_atTop.eventually_ge_atTop 0),
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).const_mul_atTop hc).eventually_ge_atTop
      (max ((65536:ℝ)^2) B₂),
    eventually_rpow_le_const_mul (show (1/3-3*(1/1000):ℝ) < 1/3 by norm_num) hc,
    eventually_tailPrime_small_localized_length hD (show 0 < 4*W^(3/2:ℝ) by positivity),
    eventually_tailPrime_small_low_upper hc hQ,
    eventually_tailPrime_small_high_upper (by norm_num : (0:ℝ) < 1/1000)
      (by norm_num : (1/1000:ℝ) < 1/12) (by norm_num : (0:ℝ) < 1)
      (by norm_num : (1:ℝ) < (1/3-3*(1/1000))*(3+1)),
    eventually_tailPrime_fixed_width_log hW m₁,
    eventually_tailPrime_fixed_width_log (by norm_num : (1:ℝ) ≤ 1) m₂,
    eventually_prime_box_range (show (0:ℝ) < 39/100-1/3 by norm_num) hη (i+j) G]
    with X hX hlog hlarge hpower hlocal hlow hcube hlog₁ hlog₂ hbox
  intro z H T hz
  dsimp only
  intro hBlo hBsq hABlo hABhi hrough hT hH hHX
  let B := largeTupleGroupLength s z
  let A := largeTupleGroupLength (Finset.univ\s) z
  have hBp : 0 < B := zero_lt_one.trans_le (largeTupleGroupLength_one s z)
  have hAp : 0 < A := zero_lt_one.trans_le (largeTupleGroupLength_one _ z)
  have hLX : 1 ≤ 1+Real.log X := by linarith
  have hBpower : X^(1/3-3*(1/1000):ℝ) ≤ B := hpower.trans hBlo
  have hquarter : X^(1/4:ℝ) ≤ B :=
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (1/4:ℝ) ≤ 1/3-3*(1/1000))).trans hBpower
  have hBsmall : (65536:ℝ)^2 ≤ B := (le_max_left _ _).trans (hlarge.trans hBlo)
  have hB₂ : B₂ ≤ B := (le_max_right _ _).trans (hlarge.trans hBlo)
  have hBX : B ≤ 3*X := by nlinarith [largeTupleGroupLength_one s z]
  have hA3 : A ≤ B^3 := by
    have hh := hcube A B hBpower hABhi
    rw [one_mul,show (2+(1:ℝ)) = ((3:ℕ):ℝ) by norm_num,Real.rpow_natCast] at hh
    exact hh
  have hHcube : H ≤ B^3 := hHX.trans (tailPrime_height_cube hX (by norm_num) hquarter)
  have hTp : 0 < T := (pow_pos (by linarith : 0 < 1+Real.log X) Ct).trans_le hT
  have hT1 : 1 ≤ T := (one_le_pow₀ hLX).trans hT
  have hTlow : (1+Real.log (W*B))^m₁ ≤ T :=
    (hlog₁ B (largeTupleGroupLength_one s z) hBX).trans
      ((pow_le_pow_right₀ hLX (le_max_left _ _)).trans hT)
  have hThecke : (1+Real.log B)^m₂ ≤ T := by
    have ht := hlog₂ B (largeTupleGroupLength_one s z) hBX
    simp only [one_mul] at ht
    exact ht.trans ((pow_le_pow_right₀ hLX (le_max_right _ _)).trans hT)
  let f := fun U => productGaussWindow (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
    (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
    (largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s)
    (largeTupleOtherCoefficient ξ z.1.1 z.1.2 s) 0 primeProductEnvelope H U z.1.1
  have htail (U : ℝ) : (∑ v ∈ Finset.range (heightWindowCount H U), f (U*(3/2:ℝ)^v)) =
      envelopeCutoffBilinearTail (largeTupleSelectedSupport ξ z.1.1 z.1.2 s)
        (largeTupleOtherSupport ξ z.1.1 z.1.2 s)
        (largeTupleSelectedCoefficient ξ z.1.1 z.1.2 s)
        (largeTupleOtherCoefficient ξ z.1.1 z.1.2 s) primeProductEnvelope H U z.1.1 := by
    unfold f productGaussWindow envelopeCutoffBilinearTail
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [productGaussHeightWindowKernel,theta_zero,one_mul]
    ring
  by_cases hs : B ≤ X^(39/100:ℝ)
  · have hAlow : 4*(W*B)^(3/2:ℝ) ≤ A := by
      rw [Real.mul_rpow (zero_le_one.trans hW) hBp.le]
      simpa only [mul_assoc] using hlocal A B hBp hABlo hs
    have hAupper : Q*A ≤ B^2*(1+Real.log B)^(3*1) := by
      simpa only [Nat.mul_one] using hlow A B hBlo hABhi
    have hb (U : ℝ) (hU : T ≤ U) :
        ‖∑ v ∈ Finset.range (heightWindowCount H U), f (U*(3/2:ℝ)^v)‖ ≤
          L₁*X^(5/6:ℝ)/(1+Real.log X)^n := by
      rw [htail]
      exact (hb₁ z H U hBsmall hAlow hAupper hA3 (hTlow.trans hU) hH hHcube).trans
        (triple_bilinear_nat_scale hX hAp.le hquarter hK₁.le hABhi n)
    obtain ⟨v,_hv,he⟩ := geometricHeight_filtered_prefix f
      (zero_lt_one.trans_le hH) hTp (X^(1/100:ℝ))
    change ‖∑ v ∈ Finset.range (heightWindowCount H T), if T*(3/2:ℝ)^v ≤ X^(1/100:ℝ) then f (T*(3/2:ℝ)^v) else 0‖ ≤ _
    rw [he]
    have hshift : T ≤ T*(3/2:ℝ)^v := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3/2)) hTp.le
    apply (norm_sub_le _ _).trans
    apply (add_le_add (hb T le_rfl) (hb _ hshift)).trans
    have hpos : 0 ≤ X^(5/6:ℝ)/(1+Real.log X)^n := by positivity
    have hc : 2*L₁ ≤ 2*L₁+D₀*L₂ := by
      have hh : 0 ≤ D₀*L₂ := by dsimp [L₂]; positivity
      linarith
    convert mul_le_mul_of_nonneg_right hc hpos using 1 <;> ring
  · have hbig : X^(39/100:ℝ) ≤ B := le_of_lt (lt_of_not_ge hs)
    have hrange := hbox A B hABlo hABhi hBsq (by
      simpa only [show (1/3+(39/100-1/3):ℝ) = 39/100 by ring] using hbig)
    have hwin (v : ℕ) :
        ‖if T*(3/2:ℝ)^v ≤ X^(1/100:ℝ) then f (T*(3/2:ℝ)^v) else 0‖ ≤
          L₂*X^(5/6:ℝ)/(1+Real.log X)^(n+1) := by
      split_ifs with hu
      · have ht : T ≤ T*(3/2:ℝ)^v := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3/2)) hTp.le
        have hub : T*(3/2:ℝ)^v ≤ B^(7/20:ℝ) := hu.trans
          ((Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (1/100:ℝ) ≤ (39/100)*(7/20))).trans (by
            rw [Real.rpow_mul (zero_le_one.trans hX)]
            exact Real.rpow_le_rpow (by positivity) hbig (by norm_num)))
        exact (hb₂ z H _ hB₂ hrough hrange.1 hrange.2 (hThecke.trans ht)
          (zero_lt_one.trans_le hH) hub).trans
          (triple_bilinear_nat_scale hX hAp.le hquarter hK₂.le hABhi (n+1))
      · rw [norm_zero]
        dsimp [L₂]
        positivity
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun v _ => hwin v)).trans
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    have hHX1 : H ≤ X := hHX.trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX
        (show (1/6+1/3000:ℝ) ≤ 1 by norm_num))
    have hN : (heightWindowCount H T:ℝ) ≤ D₀*(1+Real.log X) :=
      (hcount H T hH hT1).trans (mul_le_mul_of_nonneg_left
        (by linarith [Real.log_le_log (zero_lt_one.trans_le hH) hHX1]) hD₀.le)
    apply (mul_le_mul_of_nonneg_right hN (by dsimp [L₂]; positivity)).trans
    have he : D₀*(1+Real.log X)*(L₂*X^(5/6:ℝ)/(1+Real.log X)^(n+1)) =
        (D₀*L₂)*X^(5/6:ℝ)/(1+Real.log X)^n := by
      rw [pow_succ]
      field_simp
    rw [he]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hh : 0 ≤ L₁ := by dsimp [L₁]; positivity
    linarith

end CubicFirstMoment

end

end OAI
