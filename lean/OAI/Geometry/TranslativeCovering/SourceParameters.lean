import OAI.Geometry.TranslativeCovering.CoveringGrowth

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

namespace SourceParameters
open Filter
open scoped Topology
noncomputable def ε : ℝ := 1/1073741824
noncomputable def a : ℝ := 1+ε
noncomputable def D : ℝ := 1/1024
noncomputable def v : ℝ := 1/64
noncomputable def b (n : ℕ) : ℝ := a*(1+(n:ℝ)⁻¹)
noncomputable def rminus (n : ℕ) : ℝ := a*(1-10*Real.log n/(n:ℝ))
noncomputable def h (n : ℕ) : ℝ := RadialShell.η n/(100*(n:ℝ))
noncomputable def L (n : ℕ) : ℝ := D+b n+5*RadialShell.η n
noncomputable def Cloc : ℝ := 1000/v
noncomputable def N (n : ℕ) (R : ℝ) : ℕ := ⌈20*R/v*(L n/a)^n⌉₊
noncomputable def M (n : ℕ) : ℕ := ⌈Real.exp ((n:ℝ)*Real.log n/16)⌉₊
lemma a_pos : 0 < a := by norm_num [a,ε]
lemma a_one : 1 < a := by norm_num [a,ε]
lemma D_pos : 0 < D := by norm_num [D]
lemma L_limit : Tendsto L atTop (𝓝 (D+a)) := by
  unfold L b
  convert (tendsto_const_nhds (x := D)).add
    (((tendsto_const_nhds (x := (1:ℝ))).add RadialShell.inv_limit).const_mul a) |>.add
      (RadialShell.eta_limit.const_mul 5) using 1 ; simp
lemma base_limit : Tendsto (fun n => L n/a) atTop (𝓝 ((D+a)/a)) :=
  L_limit.div_const a
lemma base_log : Real.log ((D+a)/a) < 1/200 := by
  have hp : 0 < (D+a)/a := div_pos (add_pos D_pos a_pos) a_pos
  have hh := Real.log_le_sub_one_of_pos hp
  have he : (D+a)/a-1 < (1:ℝ)/200 := by norm_num [D,a,ε]
  exact hh.trans_lt he
lemma length_rate : ∀ᶠ n : ℕ in atTop,∀ R : ℝ,0 ≤ R → R ≤ (n:ℝ)^2 →
    (N n R:ℝ) ≤ Real.exp ((1/100:ℝ)*(n:ℝ)) := by
  have ha := a_pos
  have hv : 0 < v := by norm_num [v]
  have hb : 0 < (D+a)/a := div_pos (add_pos D_pos a_pos) a_pos
  have hx := CoveringGrowth.combined (C := 1281) hb base_limit
    (base_log.trans (by norm_num : (1:ℝ)/200<1/100)) (by norm_num) 2
  filter_upwards [hx,eventually_ge_atTop 1] with n hn hn1 R hR hRn
  have hnp : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hbase : 1 ≤ L n/a := by
    apply (le_div_iff₀ a_pos).mpr
    have hh : 0 ≤ a*(n:ℝ)⁻¹ := by positivity
    have heta : 0 ≤ RadialShell.η n := by unfold RadialShell.η; positivity
    dsimp [L,b]
    nlinarith only [D_pos,hh,heta]
  have hp : 1 ≤ (L n/a)^n := one_le_pow₀ hbase
  have hceil : (N n R:ℝ) ≤ 20*R/v*(L n/a)^n+1 := by
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ 20*R/v*(L n/a)^n)).le
  calc
    _ ≤ 20*R/v*(L n/a)^n+1 := hceil
    _ ≤ 1280*(n:ℝ)^2*(L n/a)^n+1 := by
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRn (by norm_num : (0:ℝ)≤1280)) (le_trans (by norm_num) hp)
      norm_num [v] at *
      linarith only [hh]
    _ ≤ 1281*(n:ℝ)^2*(L n/a)^n := by
      have hn2 : 1 ≤ (n:ℝ)^2 := one_le_pow₀ hnp
      have hh := mul_le_mul hn2 hp (by norm_num : (0:ℝ)≤1) (sq_nonneg (n:ℝ))
      nlinarith only [hh]
    _ ≤ _ := hn
lemma coarse_base : ∀ᶠ n : ℕ in atTop,
    0 < RadialShell.high a n*(4*Real.sqrt ε)/D ∧
    (RadialShell.high a n*(4*Real.sqrt ε)/D)^n ≤ Real.exp (-(n:ℝ)) := by
  have hε : Real.sqrt ε = 1/32768 := by
    norm_num [ε,Real.sqrt_div,Real.sqrt_eq_iff_mul_self_eq]
  have hB : 0 < a*(4*Real.sqrt ε)/D := by rw [hε]; norm_num [a,ε,D]
  have hb := (RadialShell.high_limit a).mul_const (4*Real.sqrt ε) |>.div_const D
  have hr : Real.log (a*(4*Real.sqrt ε)/D) < -1 := by
    apply Real.log_lt_iff_lt_exp hB |>.mpr
    rw [hε]
    exact (by norm_num [a,ε,D] : a*(4*(1/32768))/D < (0.36787944116:ℝ)).trans Real.exp_neg_one_gt_d9
  simpa only [neg_one_mul] using CoveringGrowth.moving_base hB hb hr
end SourceParameters

end OAI
