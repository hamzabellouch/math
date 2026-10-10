import OAI.Geometry.TranslativeCovering.RadiusLens

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace GeometryDimension
open Filter
open scoped Topology

lemma log_div_nat : Tendsto (fun n : ℕ => Real.log n/(n:ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  exact h.comp tendsto_natCast_atTop_atTop

lemma lens_threshold {l u₀ u B : ℝ} (hl : 0 < l) (hu₀ : 0 ≤ u₀)
    (hu : u₀ < u) (_hB : 0 < B) :
    ∃ n₀ : ℕ, ∀ n : ℕ,n₀ ≤ n → 2 ≤ n ∧
      2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l ∧
      B*Real.log n/(n:ℝ) < 2 ∧
      (u₀+(B+6/l)*(Real.log n/(n:ℝ)))^2+(12/l)*(Real.log n/(n:ℝ)) ≤ u^2 := by
  have hsq : u₀^2 < u^2 := by nlinarith
  have ht : Tendsto (fun n : ℕ => (u₀+(B+6/l)*(Real.log n/(n:ℝ)))^2+
      (12/l)*(Real.log n/(n:ℝ))) atTop (𝓝 (u₀^2)) := by
    convert ((tendsto_const_nhds.add (log_div_nat.const_mul (B+6/l))).pow 2).add
      (log_div_nat.const_mul (12/l)) using 1; simp
  have hsmall : ∀ᶠ n : ℕ in atTop,B*Real.log n/(n:ℝ) < 2 := by
    have htB : Tendsto (fun n : ℕ => B*(Real.log n/(n:ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using log_div_nat.const_mul B
    have h := htB.eventually_lt_const (by norm_num : (0:ℝ) < 2)
    simpa only [mul_zero,mul_div_assoc] using h
  have hd : ∀ᶠ n : ℕ in atTop,2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop (2*(1/l+1/(1-u^2))/l))
    filter_upwards [h] with n hn
    exact (div_le_iff₀ hl).mp hn
  have he : ∀ᶠ n : ℕ in atTop,2 ≤ n ∧ 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l ∧
      B*Real.log n/(n:ℝ) < 2 ∧
      (u₀+(B+6/l)*(Real.log n/(n:ℝ)))^2+(12/l)*(Real.log n/(n:ℝ)) ≤ u^2 := by
    filter_upwards [eventually_ge_atTop 2,hd,hsmall,ht.eventually_le_const hsq] with n hn hd hs he
    exact ⟨hn,hd,hs,he⟩
  exact eventually_atTop.mp he

lemma logarithm_card {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) (hmn : m ≤ n^2) :
    Real.log (2*(m:ℝ)) ≤ 3*Real.log n := by
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmpos : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have h2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hm' : (m:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast hmn
  have h3 := Real.log_le_log hmpos hm'
  rw [Real.log_pow] at h3
  rw [Real.log_mul (by norm_num) hmpos.ne']
  norm_num only [Nat.cast_ofNat] at h3
  linarith

lemma small_family {n m : ℕ} {l u₀ u B r : ℝ}
    (hn : 2 ≤ n) (hl : 0 < l) (hu₀ : 0 ≤ u₀) (_hB : 0 ≤ B)
    (hm : 1 ≤ m) (hmn : m ≤ n^2) (hr : 0 ≤ r) (hrB : r ≤ B*Real.log n)
    (hsmall : (u₀+(B+6/l)*(Real.log n/(n:ℝ)))^2+
      (12/l)*(Real.log n/(n:ℝ)) ≤ u^2) :
    (u₀+r/(n:ℝ)+2*Real.log (2*(m:ℝ))/((n:ℝ)*l))^2+
      4*Real.log (2*(m:ℝ))/((n:ℝ)*l) ≤ u^2 := by
  have hnp : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmn' : Real.log (2*(m:ℝ)) ≤ 3*Real.log n := logarithm_card hn hm hmn
  have hlog : 0 ≤ Real.log (2*(m:ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*m by omega))
  have hr' := div_le_div_of_nonneg_right hrB hnp.le
  have hlog' := div_le_div_of_nonneg_right hmn' (mul_pos hnp hl).le
  have h1 : 0 ≤ u₀+r/(n:ℝ)+2*Real.log (2*(m:ℝ))/((n:ℝ)*l) := by positivity
  have h2 : u₀+r/(n:ℝ)+2*Real.log (2*(m:ℝ))/((n:ℝ)*l) ≤
      u₀+(B+6/l)*(Real.log n/(n:ℝ)) := by
    have he : u₀+(B+6/l)*(Real.log n/(n:ℝ)) = u₀+B*Real.log n/(n:ℝ)+
        2*(3*Real.log n/((n:ℝ)*l)) := by ring
    rw [he]
    simp only [mul_div_assoc] at *
    linarith only [hr',hlog']
  have hs := (sq_le_sq₀ h1 (h1.trans h2)).mpr h2
  have h3 : 4*Real.log (2*(m:ℝ))/((n:ℝ)*l) ≤ (12/l)*(Real.log n/(n:ℝ)) := by
    have he : (12/l)*(Real.log n/(n:ℝ)) = 4*(3*Real.log n/((n:ℝ)*l)) := by ring
    rw [he]
    simp only [mul_div_assoc] at *
    linarith only [hlog']
  linarith only [hs,h3,hsmall]

end GeometryDimension

end OAI
