import OAI.Combinatorics.SparsestCut.DirectionInterpolation

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.DirectionAsymptotics
open Filter
open scoped Topology

lemma grid_card_bound (m k : ℕ) (hm : 2 ≤ m) :
    (((2*m^k+1)^m : ℕ) : ℝ) ≤ Real.exp (((k : ℝ)+2)*(m : ℝ)^2) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (1 : ℝ) ≤ (m : ℝ)^k := one_le_pow₀ (by linarith)
  have he : (m : ℝ) ≤ Real.exp m := by linarith [Real.add_one_le_exp (m : ℝ)]
  have h3 : (3 : ℝ) ≤ Real.exp m := by linarith [Real.add_one_le_exp (m : ℝ)]
  have hb : (2 : ℝ)*(m : ℝ)^k+1 ≤ Real.exp ((k+1 : ℕ)*(m : ℝ)) := by
    calc
      _ ≤ 3*(m : ℝ)^k := by linarith
      _ ≤ Real.exp m * (Real.exp m)^k := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; rw [← Real.exp_add]; congr 1; push_cast; ring
  push_cast
  calc
    _ ≤ (Real.exp ((k+1 : ℕ)*(m : ℝ)))^m := pow_le_pow_left₀ (by positivity) hb _
    _ = Real.exp (((k : ℝ)+1)*(m : ℝ)^2) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    _ ≤ _ := by apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg (m : ℝ)]

lemma polynomial_exp_tendsto_zero (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun m : ℕ => (m : ℝ)^k * Real.exp (-c*(m : ℝ))) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) c hc).comp
    tendsto_natCast_atTop_atTop
  simpa only [Real.rpow_natCast, Function.comp_def] using h

lemma large_fourier_exponent (x : ℝ) (hx : 1000000 ≤ x) :
    54*x^2 - x^4/2048 ≤ -x := by
  have hx0 : 0 ≤ x := by linarith
  have hx2 : 1000000^2 ≤ x^2 := by nlinarith
  have hprod := mul_nonneg (show 1000000^2 - (54*2048+2048 : ℝ) ≥ 0 by norm_num) (sq_nonneg x)
  have hx4 : (1000000 : ℝ)^2*x^2 ≤ x^4 := by nlinarith [mul_le_mul_of_nonneg_right hx2 (sq_nonneg x)]
  have hxx : x ≤ x^2 := by nlinarith
  nlinarith

lemma large_chart_exponent (x : ℝ) (hx : 1000000 ≤ x) :
    6*x^2 - x^3/32 ≤ -x := by
  have hh : 1000000*x^2 ≤ x^3 := by nlinarith [mul_le_mul_of_nonneg_right hx (sq_nonneg x)]
  have hxx : x ≤ x^2 := by nlinarith
  nlinarith

lemma selection_majorant_tendsto :
    Tendsto (fun m : ℕ => 2*(m : ℝ)^9*Real.exp (-(m : ℝ)/8) +
      6*(m : ℝ)^3*Real.exp (-(m : ℝ))) atTop (𝓝 0) := by
  have h1 := (polynomial_exp_tendsto_zero 9 (c := 1/8) (by norm_num)).const_mul 2
  have h2 := (polynomial_exp_tendsto_zero 3 (c := 1) (by norm_num)).const_mul 6
  convert h1.add h2 using 1
  · funext m
    simp only [show -(1/8 : ℝ)*(m : ℝ) = -(m : ℝ)/8 by ring,
      show -(1 : ℝ)*(m : ℝ) = -(m : ℝ) by ring]
    ring
  · norm_num

lemma eventual_selection_majorant : ∀ᶠ m : ℕ in atTop,
    2*(m : ℝ)^9*Real.exp (-(m : ℝ)/8) +
      6*(m : ℝ)^3*Real.exp (-(m : ℝ)) < 1 :=
  selection_majorant_tendsto.eventually (gt_mem_nhds (by norm_num))

lemma normalized_fourier_exponent {m : ℕ} (hm : 0 < m) :
    -(m : ℝ)^6*(1/(2*Real.sqrt m))^2/(2*(2*Real.sqrt m)^2) = -(m : ℝ)^4/32 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hs : (2*Real.sqrt m)^2 = 4*(m : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m)]
  rw [_root_.one_div_pow, hs]
  field_simp
  ring

lemma normalized_covariance_exponent (m : ℕ) (hm : 0 < m) :
    -(m : ℝ)^6*(1/8)^2/(2*(4*(m : ℝ))^2) = -(m : ℝ)^4/2048 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  ring

lemma probability_majorization {m : ℕ} (hm : 1000000 ≤ m) {A B : ℝ}
    (_hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : A ≤ Real.exp (6*(m : ℝ)^2)) (hB : B ≤ Real.exp (48*(m : ℝ)^2)) :
    (m : ℝ)^3*((m : ℝ)^6*(2*Real.exp (-(m : ℝ)/8)) +
      A*B*(2*Real.exp (-(m : ℝ)^4/32)) + A*(2*Real.exp (-(m : ℝ)^4/2048))) +
      A*(2*Real.exp (-(m : ℝ)^3/32)) ≤
      2*(m : ℝ)^9*Real.exp (-(m : ℝ)/8) + 6*(m : ℝ)^3*Real.exp (-(m : ℝ)) := by
  have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow : (1 : ℝ) ≤ (m : ℝ)^3 := one_le_pow₀ (by linarith)
  have hf : A*B*(2*Real.exp (-(m : ℝ)^4/32)) ≤ 2*Real.exp (-(m : ℝ)) := by
    calc
      _ ≤ Real.exp (6*(m : ℝ)^2)*Real.exp (48*(m : ℝ)^2)*
          (2*Real.exp (-(m : ℝ)^4/32)) := by gcongr
      _ = 2*Real.exp (54*(m : ℝ)^2-(m : ℝ)^4/32) := by
        rw [show 54*(m : ℝ)^2-(m : ℝ)^4/32 =
          (6*(m : ℝ)^2+48*(m : ℝ)^2)+(-(m : ℝ)^4/32) by ring, Real.exp_add, Real.exp_add]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        have := large_fourier_exponent (m : ℝ) hm'
        nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) m) 4]
  have hc : A*(2*Real.exp (-(m : ℝ)^4/2048)) ≤ 2*Real.exp (-(m : ℝ)) := by
    calc
      _ ≤ Real.exp (6*(m : ℝ)^2)*(2*Real.exp (-(m : ℝ)^4/2048)) := by gcongr
      _ = 2*Real.exp (6*(m : ℝ)^2-(m : ℝ)^4/2048) := by simp only [Real.exp_sub, neg_div, Real.exp_neg]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        have := large_fourier_exponent (m : ℝ) hm'
        nlinarith [sq_nonneg (m : ℝ)]
  have hg : A*(2*Real.exp (-(m : ℝ)^3/32)) ≤ 2*Real.exp (-(m : ℝ)) := by
    calc
      _ ≤ Real.exp (6*(m : ℝ)^2)*(2*Real.exp (-(m : ℝ)^3/32)) := by gcongr
      _ = 2*Real.exp (6*(m : ℝ)^2-(m : ℝ)^3/32) := by simp only [Real.exp_sub, neg_div, Real.exp_neg]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (large_chart_exponent _ hm')) (by norm_num)
  have hs := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (le_refl
    ((m : ℝ)^6*(2*Real.exp (-(m : ℝ)/8)))) hf) hc) (pow_nonneg (Nat.cast_nonneg m) 3)
  have he := mul_le_mul_of_nonneg_right hpow (Real.exp_pos (-(m : ℝ))).le
  have hid : (m : ℝ)^3*((m : ℝ)^6*(2*Real.exp (-(m : ℝ)/8))) =
    2*(m : ℝ)^9*Real.exp (-(m : ℝ)/8) := by ring
  nlinarith

lemma projection_failure_bound {m : ℕ} (hm : 2 ≤ m) (hlog : 0 ≤ Real.log m) :
    (m : ℝ)^6*(2*Real.exp (-(10*Real.sqrt (Real.log m))^2/2)) ≤ 1/4 := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hs : -(10*Real.sqrt (Real.log m))^2/2 = -((50 : ℕ) * Real.log m) := by
    nlinarith [Real.sq_sqrt hlog]
  rw [hs, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hm0]
  have hpow : (8 : ℝ) ≤ (m : ℝ)^44 := by
    have hh : (2 : ℝ)^44 ≤ (m : ℝ)^44 := pow_le_pow_left₀ (by norm_num) hm' _
    norm_num at hh ⊢ ; linarith
  have hid : (m : ℝ)^6*(2*((m : ℝ)^50)⁻¹) = 2/(m : ℝ)^44 := by
    field_simp
  rw [hid]
  apply (div_le_iff₀ (pow_pos hm0 _)).mpr
  linarith

lemma eventual_bias_bound : ∀ᶠ m : ℕ in atTop,
    0 < m ∧ 16*Real.exp (-(m : ℝ)/12) ≤ 1/(8*(m : ℝ)) := by
  have ht := (polynomial_exp_tendsto_zero 1 (c := 1/12) (by norm_num)).const_mul 128
  have hsmall : ∀ᶠ m : ℕ in atTop,
      128*((m : ℝ)*Real.exp (-(m : ℝ)/12)) < 1 := by
    simpa only [pow_one, mul_zero, neg_mul, one_div_mul_eq_div, neg_div] using
      ht.eventually (gt_mem_nhds (by norm_num : (128 : ℝ)*0 < 1))
  filter_upwards [hsmall, eventually_ge_atTop 1] with m hs hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  refine ⟨by omega, (le_div_iff₀ (by positivity : (0 : ℝ) < 8*(m : ℝ))).mpr ?_⟩
  nlinarith

lemma scalar_net_error {m : ℕ} (hm : 1000 ≤ m)
    (hb : 16*Real.exp (-(m : ℝ)/12) ≤ 1/(8*(m : ℝ))) :
    (1/(2*Real.sqrt m) + 16*Real.exp (-(m : ℝ)/12))/(1-1/(m : ℝ)^3) +
      (5*(m : ℝ))*(1/(m : ℝ)^3) ≤ 2/Real.sqrt m := by
  have hx : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hx0 : (0 : ℝ) < m := by linarith
  have ht : 0 < Real.sqrt m := Real.sqrt_pos.mpr hx0
  have ht2 := Real.sq_sqrt hx0.le
  have htm : Real.sqrt m ≤ (m : ℝ) := by nlinarith
  have hp3 : (8 : ℝ) ≤ (m : ℝ)^3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (show (2 : ℝ) ≤ m by linarith) 3]
  have hr : 1/(m : ℝ)^3 ≤ 1/8 := (div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by linarith)
  have hd : (7/8 : ℝ) ≤ 1-1/(m : ℝ)^3 := by linarith
  have hsmall : 1/(8*(m : ℝ)) ≤ 1/(8*Real.sqrt m) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hbs : 1/(2*Real.sqrt m) + 16*Real.exp (-(m : ℝ)/12) ≤ (5/8)/Real.sqrt m := by
    have he : 1/(2*Real.sqrt m) + 1/(8*Real.sqrt m) = (5/8)/Real.sqrt m := by ring
    linarith
  have hfirst : (1/(2*Real.sqrt m) + 16*Real.exp (-(m : ℝ)/12))/(1-1/(m : ℝ)^3) ≤
      (5/7)/Real.sqrt m := by
    calc
      _ ≤ ((5/8)/Real.sqrt m)/(7/8) := div_le_div₀ (by positivity) hbs (by norm_num) hd
      _ = _ := by ring
  have hlast : (5*(m : ℝ))*(1/(m : ℝ)^3) ≤ 1/Real.sqrt m := by
    rw [show (5*(m : ℝ))*(1/(m : ℝ)^3) = 5/(m : ℝ)^2 by field_simp ]
    apply (div_le_div_iff₀ (by positivity) ht).mpr
    nlinarith
  have hrest : (5/7)/Real.sqrt m + 1/Real.sqrt m ≤ 2/Real.sqrt m := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) ht.le
  linarith

lemma covariance_net_error {m : ℕ} (hm : 1000 ≤ m)
    (hb : 16*Real.exp (-(m : ℝ)/12) ≤ 1/(8*(m : ℝ))) :
    1/8 + 16*Real.exp (-(m : ℝ)/12) + 8*(m : ℝ)*(1/(m : ℝ)^3) ≤ 1/2 := by
  have hx : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hx0 : (0 : ℝ) < m := by linarith
  have hsm : 1/(8*(m : ℝ)) ≤ 1/8 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hh : 8*(m : ℝ)*(1/(m : ℝ)^3) ≤ 1/4 := by
    rw [show 8*(m : ℝ)*(1/(m : ℝ)^3) = 8/(m : ℝ)^2 by field_simp ]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  linarith

lemma projection_net_error {m : ℕ} (hm : 1000 ≤ m) (hl : 1 ≤ Real.log m) :
    10*Real.sqrt (Real.log m) + 2*Real.sqrt m*(1/(m : ℝ)^3) ≤
      11*Real.sqrt (Real.log m) := by
  have hx : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hx0 : (0 : ℝ) < m := by linarith
  have ht := Real.sq_sqrt hx0.le
  have htm : Real.sqrt m ≤ (m : ℝ) := by nlinarith [Real.sqrt_nonneg (m : ℝ)]
  have hs : 1 ≤ Real.sqrt (Real.log m) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ Real.log m by linarith), Real.sqrt_nonneg (Real.log m)]
  have hg : 2*Real.sqrt m*(1/(m : ℝ)^3) ≤ 1 := by
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    have hp : (m : ℝ)^2 ≤ (m : ℝ)^3 := by
      nlinarith [mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ m by linarith) (sq_nonneg (m : ℝ))]
    nlinarith
  linarith

end UniformSparsestCut.DirectionAsymptotics

end

end OAI
