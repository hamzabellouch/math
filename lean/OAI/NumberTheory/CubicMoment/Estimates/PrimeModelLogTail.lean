import OAI.NumberTheory.CubicMoment.Estimates.PrimeModelTail
import OAI.NumberTheory.CubicMoment.Estimates.HeightWindowSum

namespace OAI

/-! The model is already negligible above a sufficiently large power
of the logarithm. This leaves the genuinely low-height corrected sum. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace CubicFirstMoment

theorem prime_model_height_log_saving {C : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    {X T L M : ℝ} (hX : 1 ≤ X) (hL : 0 < L) (hTX : T ≤ X)
    (hTL : L^8 ≤ T) (hM : 0 ≤ M)
    (hP : ∀ p ∈ P, primaryPrime p ∧ norm p ≤ 4*X)
    (hc : ∀ p ∈ P, ‖c p‖ ≤ M) (ℓ : ℤ) (u : ℝ) :
    dyadicHeightMean (fun t =>
      ‖dispersionModel P (fun p => c p*theta ℓ p) (t+u)‖) T ≤
      2*Real.sqrt (720*C)*M*X^(5/6:ℝ)/L^4 := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hT : 0 < T := (pow_pos hL 8).trans_le hTL
  have hf : 1+4*X/T ≤ 5*(X/L^8) := by
    have hratio : 1 ≤ X/T := (le_div_iff₀ hT).mpr (by simpa using hTX)
    have ht : X/T ≤ X/L^8 := div_le_div_of_nonneg_left hXp.le (pow_pos hL 8) hTL
    calc
      1+4*X/T = 1+4*(X/T) := by ring
      _ ≤ 5*(X/T) := by linarith
      _ ≤ 5*(X/L^8) := by linarith
  have he : 144*C*M^2*(1+4*X/T)*X^(2/3:ℝ) ≤
      (Real.sqrt (720*C)*M*X^(5/6:ℝ)/L^4)^2 := by
    have hx : X*X^(2/3:ℝ) = X^(5/3:ℝ) := by
      nth_rw 1 [← Real.rpow_one X]
      rw [← Real.rpow_add hXp]
      norm_num
    have hx2 : (X^(5/6:ℝ))^2 = X^(5/3:ℝ) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hXp.le]
      norm_num
    calc
      _ ≤ 144*C*M^2*(5*(X/L^8))*X^(2/3:ℝ) := by gcongr
      _ = (720*C)*M^2*X^(5/3:ℝ)/L^8 := by
        rw [← hx]
        ring
      _ = _ := by
        rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt (by positivity),hx2,←pow_mul]
  have hb := dyadicHeightMean_norm_le_of_sq_le_nonneg
    (continuous_prime_model_height P c ℓ u) hT (by positivity)
    ((prime_model_height_mean_square hMV hC P c hXp hT hM hP hc ℓ u).trans he)
  convert hb using 1
  ring

theorem prime_model_cutoff_log_saving {C : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    {X T L M X₀ : ℝ} (H : ℝ) (hX : 1 ≤ X) (hL : 0 < L) (hX₀ : 0 < X₀)
    (hTX : T ≤ X) (hTL : L^8 ≤ T) (hM : 0 ≤ M)
    (hP : ∀ p ∈ P, primaryPrime p ∧ norm p ≤ 4*X)
    (hc : ∀ p ∈ P, ‖c p‖ ≤ M) (ℓ : ℤ) :
    ‖∑ p ∈ P, (c p*theta ℓ p*((norm p^(-1/6:ℝ):ℝ):ℂ))*
      heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow T t)
        (Real.log (norm p)-Real.log X₀)‖ ≤
      4*Real.sqrt (720*C)*M*X^(5/6:ℝ)/L^4 := by
  have hT : 0 < T := (pow_pos hL 8).trans_le hTL
  let f := fun t => dispersionModel P (fun p => c p*theta ℓ p) t
  have hf : Continuous f := by
    simpa only [add_zero] using continuous_prime_model_height P c ℓ 0
  have hmean : dyadicHeightMean (fun t => ‖f t‖) T ≤
      2*Real.sqrt (720*C)*M*X^(5/6:ℝ)/L^4 := by
    simpa only [add_zero] using prime_model_height_log_saving hMV hC P c
      hX hL hTX hTL hM hP hc ℓ 0
  have hpiece (Y : ℝ) :
      ‖(T:ℂ)⁻¹*(∫ t : ℝ,
        (localizedEndpointWeight H T t*Complex.exp ((-Real.log Y*t:ℝ)*Complex.I))*f t)‖ ≤
      2*Real.sqrt (720*C)*M*X^(5/6:ℝ)/L^4 := by
    apply (normalized_dyadicWeightIntegral_bound f _ hf hT (by norm_num : (0:ℝ) ≤ 1) ?_ ?_).trans
      (by simpa only [one_mul] using hmean)
    · intro t
      rw [norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]
      exact localizedEndpointWeight_norm_le H hT t
    · intro t ht
      rw [localizedEndpointWeight_zero H hT t ht,zero_mul]
  rw [finite_cutoff_window_endpoints P _ H hT hX₀]
  have he (t : ℝ) :
      (∑ p ∈ P, (c p*theta ℓ p*((norm p^(-1/6:ℝ):ℝ):ℂ))*normTwist t p) = f t := by
    unfold f dispersionModel
    apply Finset.sum_congr rfl
    intro p hp
    ring
  simp_rw [he]
  rw [mul_sub]
  exact (norm_sub_le _ _).trans ((add_le_add (hpiece X₀) (hpiece (2*X₀))).trans_eq (by ring))

theorem prime_model_log_window_sum_bound {C : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Finset Eisenstein) (c : Eisenstein → ℂ)
      (ℓ : ℤ) (X X₀ T H M : ℝ), 1 ≤ X → 0 < X₀ → 1 ≤ H →
      2*Real.pi*H ≤ X → (1+Real.log X)^8 ≤ T → 0 ≤ M →
      (∀ p ∈ P, primaryPrime p ∧ norm p ≤ 4*X) → (∀ p ∈ P, ‖c p‖ ≤ M) →
      ‖primeModelWindowSum P c ℓ H T X₀‖ ≤
        K*M*X^(5/6:ℝ)/(1+Real.log X)^3 := by
  obtain ⟨K,hK,hsum⟩ := height_window_sum_bound
  refine ⟨4*K*(Real.sqrt (720*C)+1),by positivity,?_⟩
  intro P c ℓ X X₀ T H M hX hX₀ hH hcap hT hM hP hc
  have hL1 : 1 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hL : 0 < 1+Real.log X := zero_lt_one.trans_le hL1
  have hT1 : 1 ≤ T := (one_le_pow₀ hL1).trans hT
  have hHX : H ≤ X := (le_mul_of_one_le_left (zero_le_one.trans hH)
    (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ 2*Real.pi)).trans hcap
  have hf (t : ℝ) (ht : T ≤ t) (htH : t < 2*Real.pi*H) :
      ‖∑ p ∈ P, (c p*theta ℓ p*((norm p^(-1/6:ℝ):ℝ):ℂ))*
        heightFourierIntegral (fun s => cutoffHeightMultiplier H s*heightWindow t s)
          (Real.log (norm p)-Real.log X₀)‖ ≤
      4*Real.sqrt (720*C)*M*X^(5/6:ℝ)/(1+Real.log X)^4 :=
    prime_model_cutoff_log_saving hMV hC P c H hX hL hX₀
      (htH.le.trans hcap) (hT.trans ht) hM hP hc ℓ
  have hb := hsum H T _ _ hH hT1 (by positivity) hf
  change ‖primeModelWindowSum P c ℓ H T X₀‖ ≤ _ at hb
  apply hb.trans
  calc
    _ ≤ K*(1+Real.log X)*(4*Real.sqrt (720*C)*M*X^(5/6:ℝ)/(1+Real.log X)^4) := by
      gcongr
    _ = 4*K*Real.sqrt (720*C)*(M*X^(5/6:ℝ)/(1+Real.log X)^3) := by
      field_simp
    _ ≤ (4*K*(Real.sqrt (720*C)+1))*M*X^(5/6:ℝ)/(1+Real.log X)^3 := by
      have hz : 0 ≤ M*X^(5/6:ℝ)/(1+Real.log X)^3 := by positivity
      have hs : 4*K*Real.sqrt (720*C) ≤ 4*K*(Real.sqrt (720*C)+1) := by nlinarith
      convert mul_le_mul_of_nonneg_right hs hz using 1
      ring

lemma cubic_log_saving_isLittleO :
    (fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) =o[atTop] firstMomentScale := by
  have hL : Tendsto (fun X : ℝ => 1+Real.log X) atTop atTop :=
    tendsto_const_nhds.add_atTop Real.tendsto_log_atTop
  have hi := tendsto_inv_atTop_zero.comp hL
  have hconst : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hh := (hconst.sub hi).mul (hi.pow 2)
  simp only [sub_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero] at hh
  apply Asymptotics.isLittleO_of_tendsto' ?_ ?_
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
    have hp : 0 < firstMomentScale X := div_pos
      (Real.rpow_pos_of_pos (zero_lt_one.trans hX) _) (Real.log_pos hX)
    exact fun hz => (hp.ne' hz).elim
  · apply hh.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
    have hp : 0 < X := zero_lt_one.trans hX
    have hl : 0 < Real.log X := Real.log_pos hX
    unfold firstMomentScale
    simp only [Function.comp_apply]
    field_simp [(Real.rpow_pos_of_pos hp (5/6:ℝ)).ne',hl.ne',
      show 1+Real.log X ≠ 0 by positivity]
    ring

theorem actual_prime_model_log_tail_isLittleO {C a : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (ha : 0 < a) (ha1 : a < 1)
    (T : ℝ → ℝ) (hT : ∀ᶠ X : ℝ in atTop, (1+Real.log X)^8 ≤ T X) (ℓ : ℤ) :
    (fun X : ℝ => primeModelWindowSum (primeCutoff (4*X)) (fun _ => 1)
      ℓ (X^a) (T X) X) =o[atTop] firstMomentScale := by
  obtain ⟨K,hK,hbound⟩ := prime_model_log_window_sum_bound hMV hC
  apply Asymptotics.IsBigO.trans_isLittleO (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3)
    ?_ cubic_log_saving_isLittleO
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [hT,eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0 < 1-a by linarith)).eventually_ge_atTop (2*Real.pi)] with X hT hX hgrow
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hcap : 2*Real.pi*X^a ≤ X := by
    apply (mul_le_mul_of_nonneg_right hgrow (Real.rpow_nonneg hXp.le a)).trans_eq
    rw [← Real.rpow_add hXp]
    have he : 1-a+a = (1:ℝ) := by ring
    rw [he,Real.rpow_one]
  have hb := hbound (primeCutoff (4*X)) (fun _ => 1) ℓ X X (T X) (X^a) 1
    hX hXp (Real.one_le_rpow hX ha.le) hcap hT (by norm_num)
    (fun p hp => mem_primeCutoff.mp hp) (by intro p hp; norm_num)
  have hL : 0 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  rw [Real.norm_of_nonneg (by positivity)]
  simpa only [mul_one,mul_div_assoc] using hb

end CubicFirstMoment

end

end OAI
