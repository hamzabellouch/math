import OAI.NumberTheory.TotientAsymptotic.NormalFactorBands
import OAI.NumberTheory.TotientAsymptotic.NormalHeadBand
import OAI.NumberTheory.TotientAsymptotic.ComparisonErrorBudget

namespace OAI

/-! Quantitative margins between the actual normal largest-factor bands. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma ford_band_step {x : ℝ} {i j : ℕ} (hB : 1 < B x) (hij : i<j) (hjm : j< m x) :
    fordBandScale x j ≤ rho*fordBandScale x i := by
  have him := hij.trans hjm
  have hc : 0 < bandCenterRatio x := by
    rw [← fordBandScale_div_bandScale hB him]
    exact div_pos (fordBandScale_pos (zero_lt_one.trans hB) him) (bandScale_pos him)
  rw [fordBandScale_eq_ratio_mul hB hjm,fordBandScale_eq_ratio_mul hB him]
  have hle := (bandScale_antitone x (show i+1≤j by omega)).trans (bandScale_succ_le x i)
  simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hle hc.le

lemma ford_band_antitone {x : ℝ} {i j : ℕ} (hB : 1 < B x) (hij : i≤j) (hjm : j< m x) :
    fordBandScale x j ≤ fordBandScale x i := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · have hp := fordBandScale_pos (zero_lt_one.trans hB) (hlt.trans hjm)
    exact (ford_band_step hB hlt hjm).trans (by nlinarith [rho_lt_one])

/-- Normality changes either endpoint of an actual coarse band by less than
one further percent when expressed in Ford's centers. -/
theorem collision_factor_ford_bands : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i ≤ R x H, ∀ j ∈ Finset.Icc 1 (collisionLastIndex x i), j ≤ L x H →
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η → ∀ y : ℝ,
    1 < normalityScale x i → 0 ≤ B (normalityScale x i) → normalityScale x i ≤ y →
    0 < B y → B y ≤ 2*fordBandScale x i →
    IsNormalPrime (normalityScale x i) (remainderPrime η j) → (remainderPrime η j-1 : ℕ) ≤ y →
    (22/25 : ℝ)*fordBandScale x j ≤ B (largestPrimeFactor (remainderPrime η j-1)) ∧
    B (largestPrimeFactor (remainderPrime η j-1)) ≤ (28/25 : ℝ)*fordBandScale x j := by
  filter_upwards [collision_normal_factor_bands,eventually_collision_indices] with H hnormal hind
  filter_upwards [hnormal,fordBandScale_uniform_comparison (ε := 1/100) (by norm_num),
    m_tendsto.eventually (eventually_ge_atTop H)] with x hn hc hm
  intro i hi j hj hjL η hη y hS hBS hSy hBy hByu hp hpy
  have hjm : j< m x := ((Finset.mem_Icc.mp hj).2.trans_lt (hind x hm i hi).2.2).trans_le (Nat.sub_le _ _)
  have hb := bandScale_pos hjm
  have hd := hc j hjm
  have hfl : (99/100 : ℝ)*bandScale x j < fordBandScale x j := by
    apply (lt_div_iff₀ hb).mp
    linarith [(abs_lt.mp hd).1]
  have hfu : fordBandScale x j < (101/100 : ℝ)*bandScale x j := by
    apply (div_lt_iff₀ hb).mp
    linarith [(abs_lt.mp hd).2]
  have hh := hn i hi j hj hjL η hη y hS hBS hSy hBy hByu hp hpy
  constructor <;> nlinarith [hh.1,hh.2]

lemma normal_factor_band_gap {x : ℝ} {j k l : ℕ} {u v : ℝ}
    (hB : 1 < B x) (hjk : j<k) (hkl : k≤l) (hlm : l< m x)
    (hu : (22/25 : ℝ)*fordBandScale x j ≤ u)
    (hv : v ≤ (28/25 : ℝ)*fordBandScale x k) :
    (1/4 : ℝ)*fordBandScale x l ≤ u-v := by
  have hkm := hkl.trans_lt hlm
  have hjm := hjk.trans hkm
  have hs := ford_band_step hB hjk hkm
  have hm := ford_band_antitone hB (hjk.le.trans hkl) hlm
  have hp := fordBandScale_pos (zero_lt_one.trans hB) hjm
  nlinarith [collision_rho_bounds.2]

lemma collision_rounding_margin {h : ℕ} {δ : ℝ} (hh : 4≤h)
    (hδ : δ≤2/(h : ℝ)^32) :
    (2*(h : ℝ)+10)*δ < 1/(100*(h : ℝ)^20) := by
  have hhR : (4 : ℝ)≤h := by exact_mod_cast hh
  have h0 : (0 : ℝ)<h := by linarith
  have hp : (1000 : ℝ)<(h : ℝ)^11 := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤4) hhR 11
    norm_num at hpow
    linarith
  have hpoly : 400*(h : ℝ)+2000 < (h : ℝ)^12 := by
    have hh1 : 400*(h : ℝ)+2000 ≤ 900*h := by linarith
    have hm := mul_lt_mul_of_pos_right hp h0
    nlinarith
  calc
    _ ≤ (2*(h : ℝ)+10)*(2/(h : ℝ)^32) :=
      mul_le_mul_of_nonneg_left hδ (by positivity)
    _ < _ := by
      apply (lt_div_iff₀ (by positivity : (0 : ℝ)<100*(h : ℝ)^20)).mpr
      have he : (2*(h : ℝ)+10)*(2/(h : ℝ)^32)*(100*(h : ℝ)^20)=
          (400*(h : ℝ)+2000)/(h : ℝ)^12 := by field_simp; ring
      rw [he]
      exact (div_lt_one (by positivity)).mpr hpoly

/-- The smallest factor-band margin dominates the full grid rounding cost. -/
lemma normalized_factor_margin {x y : ℝ} {i : ℕ} {h : ℕ}
    (hh : 4≤h) (hB : 1<B x) (him : i< m x)
    (hcut : 2*collisionCutoff (m x-i)< m x-i) (hhdef : h=m x-i)
    (hBy : 0<B y) (hByu : B y≤2*fordBandScale x i) :
    1/(100*(h : ℝ)^20)<(1/10 : ℝ)*fordBandScale x (collisionLastIndex x i)/B y := by
  have hpos := fordBandScale_pos (zero_lt_one.trans hB) him
  have hl := (le_div_iff₀ hpos).mp (ford_collision_layer_ratio hB him hcut).1
  rw [← hhdef] at hl
  have hhR : (4 : ℝ)≤h := by exact_mod_cast hh
  have h0 : (0 : ℝ)<h := by linarith
  have hr : (1/100 : ℝ)<rho/40 := by nlinarith [collision_rho_bounds.1]
  apply (lt_div_iff₀ hBy).mpr
  have hu := mul_le_mul_of_nonneg_left hByu (by positivity : (0 : ℝ)≤1/(100*(h : ℝ)^20))
  have ht : 1/(100*(h : ℝ)^20)*(2*fordBandScale x i) <
      (1/10 : ℝ)*(rho/(2*(h : ℝ)^20)*fordBandScale x i) := by
    have ht := mul_lt_mul_of_pos_right hr (div_pos (mul_pos (by norm_num : (0 : ℝ)<2) hpos) (pow_pos h0 20))
    convert ht using 1 <;> ring
  exact (hu.trans_lt ht).trans_le (mul_le_mul_of_nonneg_left hl (by norm_num))

end TotientAsymptotic

end

end OAI
