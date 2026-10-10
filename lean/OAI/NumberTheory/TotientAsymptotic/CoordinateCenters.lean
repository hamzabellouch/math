import OAI.NumberTheory.TotientAsymptotic.BandComparison
import OAI.NumberTheory.TotientAsymptotic.UnbandedCubeCost

namespace OAI

/-! Compare the center in a fixed truncated simplex with Ford's natural center. -/
noncomputable section
namespace TotientAsymptotic

lemma truncated_center_factorization {M N i : ℕ} (hi : i < N) (hNM : N ≤ M)
    {B E κ : ℝ} (hB : 0 < B) :
    κ*((B+E)*rho^i*(1-(i:ℝ)/N)) =
      (κ*(1+E/B)*((M:ℝ)/N)*(1-((M-N:ℕ):ℝ)/(M-i:ℕ)))*
        (B*rho^i*(1-(i:ℝ)/M)) := by
  have hN : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have hM : (M:ℝ)≠0 := by exact_mod_cast (show M≠0 by omega)
  have hMi : (M:ℝ)-i≠0 := sub_ne_zero.mpr (by exact_mod_cast (show M≠i by omega))
  rw [Nat.cast_sub hNM,Nat.cast_sub (show i ≤ M by omega)]
  field_simp [hB.ne',hN,hM,hMi]
  ring

lemma small_center_product {u v w r : ℝ}
    (hu : 1 ≤ u ∧ u ≤ (1001/1000:ℝ))
    (hv : 1 ≤ v ∧ v ≤ (1001/1000:ℝ))
    (hw : 1 ≤ w ∧ w ≤ (1001/1000:ℝ))
    (hr : (999/1000:ℝ) ≤ r ∧ r ≤ 1) :
    (99/100:ℝ) ≤ u*v*w*r ∧ u*v*w*r ≤ (101/100:ℝ) := by
  have hu0 : 0 ≤ u := zero_le_one.trans hu.1
  have hv0 : 0 ≤ v := zero_le_one.trans hv.1
  have hw0 : 0 ≤ w := zero_le_one.trans hw.1
  have hr0 : 0 ≤ r := (by norm_num : (0:ℝ) ≤ 999/1000).trans hr.1
  have hprodlo : 1 ≤ u*v*w := by
    simpa using mul_le_mul (mul_le_mul hu.1 hv.1 zero_le_one hu0)
      hw.1 zero_le_one (mul_nonneg hu0 hv0)
  have hprodhi : u*v*w ≤ (1001/1000:ℝ)^3 := by
    calc
      _ ≤ (1001/1000:ℝ)*(1001/1000)*(1001/1000) :=
        mul_le_mul (mul_le_mul hu.2 hv.2 hv0 (by norm_num)) hw.2 hw0 (by norm_num)
      _ = _ := by ring
  constructor
  · have hh := mul_le_mul_of_nonneg_right hprodlo hr0
    nlinarith only [hh,hr.1]
  · have hh := mul_le_mul hprodhi hr.2 hr0 (by positivity : (0:ℝ) ≤ (1001/1000)^3)
    norm_num at hh ⊢
    linarith only [hh]

lemma truncated_center_bounds {M N i : ℕ} (hi : i < N) (hNM : N ≤ M)
    {B E κ : ℝ} (hB : 0 < B)
    (hκ : 1 ≤ κ ∧ κ ≤ (1001/1000:ℝ))
    (hE : 0 ≤ E/B ∧ E/B ≤ (1/1000:ℝ))
    (hMN : 1 ≤ (M:ℝ)/N ∧ (M:ℝ)/N ≤ (1001/1000:ℝ))
    (htail : ((M-N:ℕ):ℝ)/(M-i:ℕ) ≤ (1/1000:ℝ)) :
    (99/100:ℝ)*(B*rho^i*(1-(i:ℝ)/M)) ≤ 
      κ*((B+E)*rho^i*(1-(i:ℝ)/N)) ∧
    κ*((B+E)*rho^i*(1-(i:ℝ)/N)) ≤ 
      (101/100:ℝ)*(B*rho^i*(1-(i:ℝ)/M)) := by
  have hm : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hscale : 0 ≤ B*rho^i*(1-(i:ℝ)/M) := by
    apply mul_nonneg (mul_nonneg hB.le (pow_pos rho_pos _).le)
    exact sub_nonneg.mpr ((div_le_one hm).mpr (by exact_mod_cast (show i ≤ M by omega)))
  have ht0 : 0 ≤ ((M-N:ℕ):ℝ)/(M-i:ℕ) := by positivity
  have hh := small_center_product hκ (show 1 ≤ 1+E/B ∧ 1+E/B ≤ (1001/1000:ℝ) by
    constructor <;> linarith only [hE.1,hE.2]) hMN
    (show (999/1000:ℝ) ≤ 1-((M-N:ℕ):ℝ)/(M-i:ℕ) ∧
      1-((M-N:ℕ):ℝ)/(M-i:ℕ) ≤ 1 by constructor <;> linarith only [htail,ht0])
  rw [truncated_center_factorization hi hNM hB]
  exact ⟨mul_le_mul_of_nonneg_right hh.1 hscale,mul_le_mul_of_nonneg_right hh.2 hscale⟩

end TotientAsymptotic

end

end OAI
