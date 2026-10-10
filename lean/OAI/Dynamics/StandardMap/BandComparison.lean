import OAI.Dynamics.StandardMap.BandCoboundary

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma zoom_nat_one (n:ℕ) : dyadicZoom (n:ℤ) (dyadicInt 1)=dyadicInt ((2:ℕ)^n) := by
  apply Subtype.ext
  simp only [dyadicZoom_val,dyadicInt_val,Int.cast_one,mul_one,zpow_natCast,Nat.cast_ofNat,Int.cast_pow,Int.cast_ofNat]
lemma zoom_neg_one_le (n:ℕ) (hn:1≤n) : (dyadicZoom (-(n:ℤ)) (dyadicInt 1):ℝ)≤1/2 := by
  rw [dyadicZoom_val,dyadicInt_val,Int.cast_one,mul_one]
  have hh : (2:ℝ)^(-(n:ℤ))≤2^(-1:ℤ) := (zpow_right_strictMono₀ (by norm_num : (1:ℝ)<2)).monotone (by omega)
  norm_num at hh ⊢; exact hh
lemma bandMoment_fine (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) {α:ℝ} (ha:0≤α) (ha1:α≤1) (n:ℕ) (hn:1≤n) :
    (bandIntensity μ (Ico 0 1)).toReal/2≤bandMoment μ α (-(n:ℤ)) :=
  band_fine_lower μ hs hT ha ha1 _ (zoom_one_pos _) (zoom_neg_one_le n hn)
lemma bandMoment_coarse (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ)
    (htree:∀ᵐd ∂μ,TreeArray d.val) (hcan:∀ᵐd ∂μ,NoFastCancellation (realArray d.val) (1/100000000))
    {α:ℝ} (ha:0≤α) (ha1:α≤1) (n:ℕ) (hn:1200000004/((2:ℝ)^n)≤1/10000) :
    bandMoment μ α (n:ℤ)≤4*(α*1200000004)*(bandIntensity μ (Ico 0 1)).toReal := by
  unfold bandMoment
  rw [zoom_nat_one]
  have hp:0<(2:ℕ)^n := pow_pos (by norm_num) _
  have hb:=band_coarse_upper μ hs hT htree hcan ha ha1 (2^n) hp (by exact_mod_cast hn)
  refine hb.trans ?_
  have hh:(1:ℝ)≤2^n := one_le_pow₀ (by norm_num)
  have haC:0≤α*1200000004 := mul_nonneg ha (by norm_num)
  have hv : (α*1200000004/(2:ℝ)^n)*((2:ℝ)^n+3)≤4*(α*1200000004) := by
    rw [div_mul_eq_mul_div,div_le_iff₀ (pow_pos (by norm_num) _)]; nlinarith
  convert mul_le_mul_of_nonneg_right hv (ENNReal.toReal_nonneg) using 1 ; norm_cast
lemma bandMoment_order (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ)
    (htree:∀ᵐd ∂μ,TreeArray d.val) (hcan:∀ᵐd ∂μ,NoFastCancellation (realArray d.val) (1/100000000))
    {α:ℝ} (ha:0≤α) (ha1:α≤1) (hasmall:α*1200000004≤1/16) :
    ∀ᶠn:ℕ in atTop, bandMoment μ α (n:ℤ)≤bandMoment μ α (-(n:ℤ)) := by
  have hp:Tendsto (fun n:ℕ => (2:ℝ)^n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have he:∀ᶠn:ℕ in atTop,1200000004/(2:ℝ)^n≤1/10000 := by
    filter_upwards [hp.eventually (eventually_ge_atTop (1200000004*10000:ℝ))] with n hn
    rw [div_le_iff₀ (pow_pos (by norm_num) _)]; linarith
  filter_upwards [he,eventually_ge_atTop (1:ℕ)] with n hn hn1
  have h1:=bandMoment_coarse μ hs hT htree hcan ha ha1 n hn
  have h2:=bandMoment_fine μ hs hT ha ha1 n hn1
  refine le_trans h1 (le_trans ?_ h2)
  have hI:=ENNReal.toReal_nonneg (a:=bandIntensity μ (Ico 0 1))
  nlinarith [mul_nonneg (by linarith : 0≤1/2-4*(α*1200000004)) hI]
end StandardMapEntropy

end OAI
