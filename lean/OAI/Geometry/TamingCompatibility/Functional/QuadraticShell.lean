import Mathlib

namespace OAI


noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace QuadraticShell

def profile (r : ℝ) (d : ℝ≥0∞) : ℝ≥0∞ := (1 + d / ENNReal.ofReal r)⁻¹ ^ 6

lemma exists_dyadic_majorant {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) :
    ∃ n : ℕ, d < 2^(n+1)*r ∧ (1+d/r)⁻¹^6 ≤ (1/64:ℝ)^n := by
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near (le_max_left 1 (d/r)) (by norm_num : (1:ℝ)<2)
  have hbase : (2:ℝ)^n ≤ 1+d/r := hn.trans (max_le (le_add_of_nonneg_right (div_nonneg hd hr.le)) (by linarith))
  refine ⟨n,(div_lt_iff₀ hr).mp ((le_max_right 1 (d/r)).trans_lt hn'),?_⟩
  calc
    (1+d/r)⁻¹^6 ≤ ((2:ℝ)^n)⁻¹^6 := by
      gcongr
    _ = (1/64:ℝ)^n := by
      rw [← inv_pow,← pow_mul,Nat.mul_comm,pow_mul,inv_pow]
      norm_num

lemma profile_ofReal {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) :
    profile r (ENNReal.ofReal d) = ENNReal.ofReal ((1+d/r)⁻¹^6) := by
  simp only [profile, ← ENNReal.ofReal_div_of_pos hr, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (div_nonneg hd hr.le)]
  rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_pow (by positivity)]

lemma profile_top {r : ℝ} : profile r ⊤ = 0 := by
  simp [profile, ENNReal.top_div]

lemma profile_majorant {r : ℝ} (hr : 0 < r) (d : ℝ≥0∞) :
    profile r d ≤ ∑' n : ℕ,
      {e : ℝ≥0∞ | e < ENNReal.ofReal (2^(n+1)*r)}.indicator
        (fun _ => ENNReal.ofReal ((1/64:ℝ)^n)) d := by
  by_cases hd : d = ⊤
  · rw [hd,profile_top]; exact bot_le
  obtain ⟨n,hn,hbound⟩ := exists_dyadic_majorant hr d.toReal_nonneg
  have hdreal : ENNReal.ofReal d.toReal = d := ENNReal.ofReal_toReal hd
  have hn' : d < ENNReal.ofReal (2^(n+1)*r) := by
    rw [←hdreal]
    exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr hn
  calc
    _ = ENNReal.ofReal ((1+d.toReal/r)⁻¹^6) := by rw [←hdreal,profile_ofReal hr d.toReal_nonneg]; simp [hdreal]
    _ ≤ ENNReal.ofReal ((1/64:ℝ)^n) := ENNReal.ofReal_le_ofReal hbound
    _ = _ := by simp only [indicator, mem_ofPred_eq, hn', ↓reduceIte]
    _ ≤ _ := ENNReal.le_tsum n

lemma dyadic_term_identity (C r : ℝ) (n : ℕ) :
    (1/64:ℝ)^n*(C*(2^(n+1)*r)^2) = 4*C*r^2*(1/16:ℝ)^n := by
  have hpow : ((2:ℝ)^n)^2 = ((2:ℝ)^2)^n := by
    rw [← pow_mul,← pow_mul,Nat.mul_comm]
  calc
    _ = 4*C*r^2*((1/64:ℝ)^n*((2:ℝ)^2)^n) := by rw [pow_succ,←hpow]; ring
    _ = _ := by rw [←mul_pow]; norm_num

theorem lintegral_profile_le {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (δ : Y → ℝ≥0∞) (hδ : Measurable δ)
    (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℝ, 0 < s → μ.real {y | δ y < ENNReal.ofReal s} ≤ C*s^2)
    {r : ℝ} (hr : 0 < r) :
    ∫⁻ y, profile r (δ y) ∂μ ≤ ENNReal.ofReal (8*C*r^2) := by
  let f : ℕ → Y → ℝ≥0∞ := fun n =>
    {y | δ y < ENNReal.ofReal (2^(n+1)*r)}.indicator
      (fun _ => ENNReal.ofReal ((1/64:ℝ)^n))
  have hf : ∀ n, Measurable (f n) := fun n =>
    measurable_const.indicator (measurableSet_lt hδ measurable_const)
  have hi (n : ℕ) : ∫⁻ y, f n y ∂μ ≤ ENNReal.ofReal (4*C*r^2*(1/16:ℝ)^n) := by
    rw [lintegral_indicator_const (measurableSet_lt hδ measurable_const)]
    have hm : μ {y | δ y < ENNReal.ofReal (2^(n+1)*r)} ≤
        ENNReal.ofReal (C*(2^(n+1)*r)^2) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
      exact ENNReal.ofReal_le_ofReal (hgrowth _ (by positivity))
    calc
      _ ≤ ENNReal.ofReal ((1/64:ℝ)^n) * ENNReal.ofReal (C*(2^(n+1)*r)^2) :=
        by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), dyadic_term_identity]
  calc
    _ ≤ ∫⁻ y, ∑' n, f n y ∂μ := lintegral_mono fun y => profile_majorant hr (δ y)
    _ = ∑' n, ∫⁻ y, f n y ∂μ := lintegral_tsum fun n => (hf n).aemeasurable
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (4*C*r^2*(1/16:ℝ)^n) := ENNReal.tsum_le_tsum hi
    _ = ENNReal.ofReal (4*C*r^2) * (1-ENNReal.ofReal (1/16))⁻¹ := by
      simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4*C*r^2), ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤1/16)]
      rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric]
    _ ≤ ENNReal.ofReal (8*C*r^2) := by
      have hratio : (1-ENNReal.ofReal (1/16))⁻¹ ≤ ENNReal.ofReal 2 := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : (0:ℝ) ≤ 1/16)]
        rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 1-1/16)]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
      calc
        _ ≤ ENNReal.ofReal (4*C*r^2)*ENNReal.ofReal 2 := by gcongr
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

end QuadraticShell

end

end OAI
