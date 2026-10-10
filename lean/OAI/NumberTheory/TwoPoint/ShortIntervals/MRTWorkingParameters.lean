import OAI.NumberTheory.TwoPoint.Fourier.MajorArcWorkingBand
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWorkingOuterScale
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTQuotientFinalBand

namespace OAI

/-! The literal first prime band, working length and common final band.
The W and X thresholds are independent of the original short length. -/

namespace TwoPointCorrelations

open Filter Finset

theorem mrt_working_prime_parameters :
    ∀ᶠ W : ℝ in atTop, 2 ≤ W ∧ ∀ H : ℕ, 0 < H →
      1 ≤ Real.log (H:ℝ) → W ≤ Real.log (H:ℝ)^5 →
      let P := W^(500000:ℕ)
      let Q := (majorArcWorkingLength H W:ℝ)/W^3
      2 ≤ P ∧ P ≤ Q ∧ 2 ≤ Real.log P ∧ 1 ≤ Real.log Q ∧
        8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P ∧
        W^100 ≤ mrtBaseResolution P Q (1/100) ∧
        2 ≤ mrtBaseResolution P Q (1/100) := by
  filter_upwards [major_arc_working_length_power 500003,eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (10:ℝ))]
    with W hpower hW hlog
  refine ⟨hW,?_⟩
  intro H hH hLH hWH
  let P := W^(500000:ℕ)
  let Q := (majorArcWorkingLength H W:ℝ)/W^3
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := by linarith
  have hlarge := hpower H hH hLH hWH
  have hP : 2 ≤ P := hW.trans (le_self_pow₀ hW1 (by decide))
  have hPQ : P ≤ Q := by
    apply (le_div_iff₀ (pow_pos hW0 3)).mpr
    change W^500000*W^3 ≤ (majorArcWorkingLength H W:ℝ)
    simpa only [← pow_add] using hlarge
  have hLP : 2 ≤ Real.log P := by
    change 2 ≤ Real.log (W^(500000:ℕ))
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hLQ : 1 ≤ Real.log Q :=
    (show (1:ℝ)≤2 by norm_num).trans (hLP.trans
      (Real.log_le_log (by linarith : 0<P) hPQ))
  have hQ : 1 < Q := lt_of_lt_of_le (by norm_num : (1:ℝ)<2) (hP.trans hPQ)
  have hQH : Q ≤ (majorArcWorkingLength H W:ℝ) :=
    div_le_self (Nat.cast_nonneg _) (one_le_pow₀ hW1)
  have hbudget := major_arc_working_band_budget 500000 le_rfl hlog hW0 hQ hQH
  have hres := major_arc_working_band_resolution 500000 le_rfl hW1 hQ hQH
  exact ⟨hP,hPQ,hLP,hLQ,hbudget,hres,
    (hW.trans (le_self_pow₀ hW1 (by decide))).trans hres⟩

theorem mrt_working_outer_parameters :
    ∀ᶠ X : ℕ in atTop, ∀ W : ℝ, 2 ≤ W →
      W ≤ (Real.log (X:ℝ))^(1/125:ℝ) → ∀ H : ℕ,
      let Q := (majorArcWorkingLength H W:ℝ)/W^3
      0 < Q → Real.log Q ≤ Real.sqrt (Real.log X)/2 ∧
        2*Q ≤ (⌈Real.sqrt (X:ℝ)⌉₊:ℝ) := by
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<623/1250 by norm_num)).eventually
    (eventually_ge_atTop (2:ℝ))
  filter_upwards [hlog.eventually hp,hlog.eventually (eventually_ge_atTop (1:ℝ)),
    mrt_working_length_add_two_below_sqrt] with X hp hL hlength
  change 2 ≤ (Real.log (X:ℝ))^(623/1250:ℝ) at hp
  intro W hW hWX H
  dsimp only
  intro hQ
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := by linarith
  have hL0 : 0 < Real.log (X:ℝ) := by linarith
  have hroot : W^(1/5:ℝ) ≤ Real.sqrt (Real.log X)/2 := by
    have he : (Real.log (X:ℝ))^(1/625:ℝ)*
        (Real.log (X:ℝ))^(623/1250:ℝ)=Real.sqrt (Real.log X) := by
      rw [← Real.rpow_add hL0,Real.sqrt_eq_rpow]
      norm_num
    have hm := mul_le_mul_of_nonneg_left hp
      (Real.rpow_nonneg hL0.le (1/625))
    rw [he] at hm
    have hw : W^(1/5:ℝ) ≤ (Real.log (X:ℝ))^(1/625:ℝ) := by
      calc
        _ ≤ ((Real.log (X:ℝ))^(1/125:ℝ))^(1/5:ℝ) :=
          Real.rpow_le_rpow hW0.le hWX (by norm_num)
        _ = _ := by rw [← Real.rpow_mul hL0.le]; norm_num
    linarith
  have hQH : (majorArcWorkingLength H W:ℝ)/W^3 ≤ (majorArcWorkingLength H W:ℝ) :=
    div_le_self (Nat.cast_nonneg _) (one_le_pow₀ hW1)
  constructor
  · have hh := Real.log_le_log hQ
      (hQH.trans (major_arc_working_length_exp_upper H hW0.le))
    rw [Real.log_exp] at hh
    exact hh.trans hroot
  · have hW3 : (2:ℝ) ≤ W^3 := hW.trans (le_self_pow₀ hW1 (by decide))
    have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg (majorArcWorkingLength H W))
      (by norm_num : (0:ℝ)<2) hW3
    have hc : (majorArcWorkingLength H W:ℝ)+2 ≤ (⌈Real.sqrt (X:ℝ)⌉₊:ℝ) := by
      exact_mod_cast hlength W hW1 hWX H
    linarith

theorem mrt_working_parameters :
    ∃ W₀ : ℝ, ∃ X₀ : ℕ, ∀ W : ℝ, W₀ ≤ W →
    ∀ H : ℕ, 0 < H → 1 ≤ Real.log (H:ℝ) → W ≤ Real.log (H:ℝ)^5 →
    ∀ X : ℕ, X₀ ≤ X → W ≤ (Real.log (X:ℝ))^(1/125:ℝ) →
      let P := W^(500000:ℕ)
      let Q := (majorArcWorkingLength H W:ℝ)/W^3
      (2 ≤ P ∧ P ≤ Q ∧ 2 ≤ Real.log P ∧ 1 ≤ Real.log Q ∧
        8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P ∧
        W^100 ≤ mrtBaseResolution P Q (1/100) ∧ 2 ≤ mrtBaseResolution P Q (1/100)) ∧
      (Real.log Q ≤ Real.sqrt (Real.log X)/2 ∧ 2*Q ≤ (⌈Real.sqrt (X:ℝ)⌉₊:ℝ)) ∧
      ∃ J : ℕ, 1 ≤ J ∧
        200*Real.log (Real.log (4*(X:ℝ)))+1 ≤ Real.log (mrtBandLower P Q J) ∧
        Real.sqrt (Real.log X)/2 < Real.log (mrtBandUpper Q (J+1)) ∧
        (∀ i ∈ Icc 1 J, Real.log (mrtBandUpper Q i) ≤ Real.sqrt (Real.log X)/2) ∧
        ∀ n : ℕ, ⌈Real.sqrt (X:ℝ)⌉₊ ≤ n → n ≤ 4*X →
          200*Real.log (Real.log n)+1 ≤ Real.log (mrtBandLower P Q J) ∧
          ∀ i ∈ Icc 1 J, mrtBandUpper Q i ≤ Real.exp (Real.sqrt (Real.log n)) := by
  obtain ⟨W₀,hW₀⟩ := Filter.eventually_atTop.mp mrt_working_prime_parameters
  obtain ⟨X₀,hX₀⟩ := Filter.eventually_atTop.mp
    (mrt_working_outer_parameters.and mrt_quotient_common_final_band)
  refine ⟨W₀,X₀,?_⟩
  intro W hW H hH hLH hWH X hX hWX
  have hw := hW₀ W hW
  have hb := hw.2 H hH hLH hWH
  let P := W^(500000:ℕ)
  let Q := (majorArcWorkingLength H W:ℝ)/W^3
  have hQ : 0 < Q := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (hb.1.trans hb.2.1)
  have hx := hX₀ X hX
  have ho := hx.1 W hw.1 hWX H hQ
  refine ⟨hb,ho,?_⟩
  exact hx.2 P Q ((show (1:ℝ)≤2 by norm_num).trans hb.2.2.1)
    hb.2.2.2.1 ho.1 hb.2.2.2.2.1

end TwoPointCorrelations

end OAI
