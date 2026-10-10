import OAI.Geometry.TranslativeCovering.EntropyRates

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

namespace LocalizationRates
open Filter SourceParameters Metric MeasureTheory
open scoped Topology ENNReal
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable def β (n : ℕ) : ℝ := b n+4*RadialShell.η n
noncomputable def W (n : ℕ) : ℝ := D+b n+4*RadialShell.η n
noncomputable def rround (n : ℕ) : ℝ := rminus n-2*RadialShell.η n
lemma n_eta_limit : Tendsto (fun n : ℕ => (n:ℝ)*RadialShell.η n) atTop (𝓝 0) := by
  have he (n : ℕ) : (n:ℝ)*RadialShell.η n = ((n:ℝ)⁻¹)^3 := by
    by_cases hn : n=0
    · subst n; norm_num [RadialShell.η]
    · have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn
      dsimp [RadialShell.η]; field_simp
  simpa only [he,zero_pow (by norm_num : 3≠0)] using RadialShell.inv_limit.pow 3
lemma rminus_limit : Tendsto rminus atTop (𝓝 a) := by
  convert ((tendsto_const_nhds (x := (1:ℝ))).sub (RadialShell.log_div_limit.const_mul 10)).const_mul a using 1 <;>
    first | rfl | simp only [mul_zero,sub_zero,mul_one] | (funext n; dsimp [rminus]; ring)
lemma ball_scale {n : ℕ} {a r : ℝ} (ha : 0<a) (hr : 0≤r) :
    volume (closedBall (0:Space n) r) = ENNReal.ofReal ((r/a)^n)*volume (closedBall (0:Space n) a) := by
  rw [volume.addHaar_closedBall _ hr,volume.addHaar_closedBall _ ha.le]
  simp only [finrank_euclideanSpace,Fintype.card_fin]
  rw [← mul_assoc,← ENNReal.ofReal_mul (pow_nonneg (div_nonneg hr ha.le) _)]
  congr 2
  rw [div_pow,div_mul_cancel₀ _ (pow_ne_zero _ ha.ne')]
lemma outer_rate : ∀ᶠ n : ℕ in atTop,0 < β n ∧ (β n/a)^n ≤ 3 := by
  have hlog3 : 1 < Real.log 3 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr
    (Real.exp_one_lt_d9.trans (by norm_num))
  have ht : Tendsto (fun n : ℕ => 1+4*(n:ℝ)*RadialShell.η n/a) atTop (𝓝 1) := by
    convert (tendsto_const_nhds (x := (1:ℝ))).add ((n_eta_limit.const_mul 4).div_const a) using 1 <;> (try funext n) <;> ring_nf
  filter_upwards [ht.eventually_le_const hlog3,eventually_ge_atTop 1] with n hn hn1
  have hnp : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have ha := a_pos
  have hβ : 0 < β n := by dsimp [β,b,RadialShell.η]; positivity
  refine ⟨hβ,?_⟩
  have hb : 0 < β n/a := div_pos hβ ha
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hb) hnp.le
  have he : (n:ℝ)*(β n/a-1) = 1+4*(n:ℝ)*RadialShell.η n/a := by
    dsimp [β,b]; field_simp ; ring
  rw [he] at hlog
  calc
    _ = Real.exp ((n:ℝ)*Real.log (β n/a)) := by rw [Real.exp_nat_mul,Real.exp_log hb]
    _ ≤ Real.exp (Real.log 3) := Real.exp_le_exp.mpr (hlog.trans hn)
    _ = _ := Real.exp_log (by norm_num)
lemma inner_rate : ∀ᶠ n : ℕ in atTop,0 < rminus n ∧
    (n:ℝ)^2/(2*v)*(rminus n/a)^n ≤ 1/200 := by
  filter_upwards [rminus_limit.eventually (lt_mem_nhds a_pos),eventually_ge_atTop 10] with n hr hn
  have hnp : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have h10 : (10:ℝ)≤n := by exact_mod_cast hn
  have ha := a_pos
  have hb : 0<rminus n/a := div_pos hr ha
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hb) hnp.le
  have he : (n:ℝ)*(rminus n/a-1) = -10*Real.log n := by dsimp [rminus]; field_simp ; ring
  rw [he] at hlog
  have hp : (rminus n/a)^n ≤ ((n:ℝ)⁻¹)^10 := by
    calc
      _ = Real.exp ((n:ℝ)*Real.log (rminus n/a)) := by rw [Real.exp_nat_mul,Real.exp_log hb]
      _ ≤ Real.exp (-10*Real.log n) := Real.exp_le_exp.mpr hlog
      _ = _ := by rw [show -10*Real.log n = -(10*Real.log n) by ring,Real.exp_neg,show Real.exp (10*Real.log n) = (n:ℝ)^10 by simpa using Real.exp_nat_mul (Real.log n) 10 |>.trans (by rw [Real.exp_log hnp])]; simp only [inv_pow]
  refine ⟨hr,?_⟩
  calc
    _ ≤ (n:ℝ)^2/(2*v)*((n:ℝ)⁻¹)^10 := mul_le_mul_of_nonneg_left hp (by norm_num [v]; positivity)
    _ = 32/((n:ℝ)^8) := by norm_num [v]; field_simp
    _ ≤ _ := by
      apply (div_le_iff₀ (pow_pos hnp 8)).mpr
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤10) h10 8
      norm_num at hh ⊢
      linarith only [hh]
lemma dimension : ∀ᶠ n : ℕ in atTop,1≤n ∧ 0<rminus n ∧ 0<β n ∧
    (β n/a)^n≤3 ∧ (n:ℝ)^2/(2*v)*(rminus n/a)^n≤1/200 ∧
    (2*(n:ℝ)/a)*(Real.sqrt n*h n/2)≤1 := by
  have ht : Tendsto (fun n : ℕ => 2*(n:ℝ)*RadialShell.η n/a) atTop (𝓝 0) := by
    convert (n_eta_limit.const_mul 2).div_const a using 1 <;> (try funext n) <;> ring_nf
  filter_upwards [outer_rate,inner_rate,eventually_ge_atTop 1,ht.eventually_le_const (by norm_num : (0:ℝ)<1)] with n ho hi hn ht
  refine ⟨hn,hi.1,ho.1,ho.2,hi.2,?_⟩
  calc
    _ ≤ (2*(n:ℝ)/a)*RadialShell.η n := mul_le_mul_of_nonneg_left (EntropyRates.error_bound hn) (by have := a_pos; positivity)
    _ ≤ _ := by simpa only [div_mul_eq_mul_div] using ht
end LocalizationRates

end OAI
