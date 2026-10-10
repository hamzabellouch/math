import OAI.NumberTheory.TotientAsymptotic.PPTComparisonGrid
import OAI.NumberTheory.TotientAsymptotic.PPTGridError

namespace OAI

/-!
The quantitative margins for the actual PPT paired grid.  The last
retained coordinates have size at least `t^(-1/3)`; their inverse-cube
relative gaps dominate the normality mesh when the dimension is
logarithmic in `t`.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- A left-coordinate gap survives both alignment errors and the stated
grid padding. -/
lemma ppt_paired_gap_of_left_gap {u v u' v' A B padding : ℝ}
    (hprev : |u-v| ≤ A) (hnext : |u'-v'| ≤ B)
    (hgap : u'+A+B+padding < u) :
    max u' v'+padding < min u v := by
  have hA : 0 ≤ A := (abs_nonneg _).trans hprev
  have hB : 0 ≤ B := (abs_nonneg _).trans hnext
  have hmin : u-A ≤ min u v := le_min (by linarith) (by linarith [(abs_le.mp hprev).2])
  have hmax : max u' v' ≤ u'+B := max_le (by linarith) (by linarith [(abs_le.mp hnext).1])
  linarith

/-- A genuine head-to-tail gap supplies an adaptive lower endpoint. -/
lemma ppt_adaptive_head_edge {first u v : ℝ}
    (hgap : first < min u v) (htop : max u v ≤ 1) :
    ∃ θ : ℝ, first < θ ∧ θ ≤ min u v ∧ θ < 1 := by
  refine ⟨(first+min u v)/2, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · have hh : min u v ≤ 1 := (min_le_left _ _).trans ((le_max_left _ _).trans htop)
    linarith

lemma ppt_contraction_gap {u v e ω : ℝ} (hu : 0 ≤ u) (hω : 0 < ω)
    (hω1 : ω ≤ 1) (hcontract : v ≤ u/(1+ω)+e) :
    ω*u/2-e ≤ u-v := by
  have hden : 0 < 1+ω := by linarith
  have hrec : 1/(1+ω) ≤ 1-ω/2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hrec hu
  have hbound : u/(1+ω) ≤ (1-ω/2)*u := by
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hh
  nlinarith

/-- The entire grid-padding cost is smaller than a fixed fraction of the
last retained coordinate's inverse-cube gap, uniformly in the dimension. -/
theorem ppt_log_dimension_separation {C : ℝ} (_hC : 0 < C) :
    ∀ᶠ t : ℝ in atTop, ∀ H : ℕ,
      1 ≤ H → (H : ℝ) ≤ C*Real.log t →
      (8*(H : ℝ)+20)*(2*(Real.log t)^5/Real.sqrt t) <
        1/(40*(H : ℝ)^3*t^(1/3 : ℝ)) := by
  have hlim : Tendsto (fun t : ℝ => (Real.log t)^9/t^(1/6 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (9 : ℕ)
        (show (0 : ℝ) < 1/6 by norm_num)).tendsto_div_nhds_zero
  have hscaled : Tendsto (fun t : ℝ =>
      2240*C^4*((Real.log t)^9/t^(1/6 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul (2240*C^4)
  filter_upwards [hscaled.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (1 : ℝ)] with t ht ht1
  intro H hH hdim
  have ht0 : 0 < t := zero_lt_one.trans ht1
  have hlog : 0 < Real.log t := Real.log_pos ht1
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := zero_lt_one.trans_le hHR
  have hthird : 0 < t^(1/3 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hsixth : 0 < t^(1/6 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hprod : t^(1/3 : ℝ)*t^(1/6 : ℝ) = Real.sqrt t := by
    rw [← Real.rpow_add ht0, Real.sqrt_eq_rpow]
    norm_num
  have hratio : t^(1/3 : ℝ)/Real.sqrt t = 1/t^(1/6 : ℝ) := by
    apply (div_eq_div_iff hsqrt.ne' hsixth.ne').mpr
    simpa only [one_mul] using hprod
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg H) hdim 4
  apply (lt_div_iff₀ (by positivity : 0 < 40*(H : ℝ)^3*t^(1/3 : ℝ))).mpr
  calc
    _ ≤ (28*(H : ℝ))*(2*(Real.log t)^5/Real.sqrt t)*
        (40*(H : ℝ)^3*t^(1/3 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 2240*(H : ℝ)^4*(Real.log t)^5/t^(1/6 : ℝ) := by
      calc
        _ = 2240*(H : ℝ)^4*(Real.log t)^5*(t^(1/3 : ℝ)/Real.sqrt t) := by ring
        _ = _ := by rw [hratio]; ring
    _ ≤ 2240*(C*Real.log t)^4*(Real.log t)^5/t^(1/6 : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num))
          (by positivity)) hsixth.le
    _ = 2240*C^4*((Real.log t)^9/t^(1/6 : ℝ)) := by ring
    _ < 1 := ht

/-- The additive logarithmic factor-count error can be included by
doubling the square-root mesh. -/
theorem ppt_logarithmic_alignment_error :
    ∀ᶠ t : ℝ in atTop,
      Real.log (3*t)/t ≤ (Real.log t)^5/Real.sqrt t := by
  have hlog : Tendsto (fun t : ℝ => Real.log t/Real.sqrt t) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow, Real.rpow_natCast, pow_one] using
      (isLittleO_log_rpow_rpow_atTop (1 : ℕ)
        (show (0 : ℝ) < 1/2 by norm_num)).tendsto_div_nhds_zero
  have hconst : Tendsto (fun t : ℝ => Real.log 3/Real.sqrt t) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)))
  have hsum : Tendsto (fun t : ℝ => (Real.log 3+Real.log t)/Real.sqrt t)
      atTop (𝓝 0) := by
    simpa only [← add_div, zero_add] using hconst.add hlog
  filter_upwards [hsum.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with t ht htlog ht1
  have ht0 : 0 < t := zero_lt_one.trans ht1
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hlog3 : Real.log (3*t) = Real.log 3+Real.log t :=
    Real.log_mul (by norm_num) ht0.ne'
  have hnum : Real.log (3*t) ≤ Real.sqrt t := by
    rw [hlog3]
    exact ((div_lt_one hsqrt).mp ht).le
  have hpower : (1 : ℝ) ≤ (Real.log t)^5 := one_le_pow₀ htlog
  calc
    _ ≤ Real.sqrt t/t := div_le_div_of_nonneg_right hnum ht0.le
    _ = 1/Real.sqrt t := by rw [Real.sqrt_div_self, one_div]
    _ ≤ (Real.log t)^5/Real.sqrt t := div_le_div_of_nonneg_right hpower hsqrt.le

/-- The doubled mesh also fits in the inverse-cube exponent margin. -/
theorem ppt_grid_error_absorbed_two_mesh {C : ℝ} (hC : 0 < C) :
    ∀ᶠ t : ℝ in atTop, ∀ (b H r : ℕ) (e w η δ : ℝ),
      1 ≤ H → b ≤ H → r+1 ≤ H → (H : ℝ) ≤ C*Real.log t →
      0 ≤ δ → δ ≤ 2*((Real.log t)^5/Real.sqrt t) →
      e ≤ (2*(b : ℝ)+4)*δ → w ≤ (4*(b : ℝ)+3)*δ → η ≤ δ →
      e*(∑ j ∈ Finset.Icc 1 (b-1), a j)+2*(b-1 : ℕ)*w+
        η*(∑ i ∈ Finset.Icc 2 b, ((i : ℝ)*Real.log i+i)) ≤
          rowContractionError r/16 := by
  filter_upwards [ppt_log_dimension_mesh_budget (C := 2*C) (by positivity),
    eventually_gt_atTop (1 : ℝ)] with t ht ht1
  intro b H r e w η δ hH hbH hrH hdim hδ hδmax he hw hη
  have hlog : 0 < Real.log t := Real.log_pos ht1
  have hmesh : 0 ≤ (Real.log t)^5/Real.sqrt t := by positivity
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hdim' : ((2*H : ℕ) : ℝ) ≤ (2*C)*Real.log t := by
    push_cast
    linarith
  have hbudget := ht (2*H) (by omega) hdim'
  apply (ppt_grid_error_polynomial_bound hH hbH hδ he hw hη).trans
  calc
    _ ≤ 32*(H : ℝ)^3*(2*((Real.log t)^5/Real.sqrt t)) :=
      mul_le_mul_of_nonneg_left hδmax (by positivity)
    _ ≤ 32*((2*H : ℕ) : ℝ)^3*((Real.log t)^5/Real.sqrt t) := by
      push_cast
      have hp : 0 ≤ (H : ℝ)^3*((Real.log t)^5/Real.sqrt t) := by positivity
      nlinarith only [hp]
    _ ≤ 1/(80*((2*H : ℕ) : ℝ)^3) := hbudget
    _ ≤ 1/(80*(r+1 : ℝ)^3) := by
      have hr : (r+1 : ℝ) ≤ ((2*H : ℕ) : ℝ) := by exact_mod_cast (show r+1 ≤ 2*H by omega)
      exact one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hr 3) (by norm_num))
    _ = rowContractionError r/16 := by
      unfold rowContractionError
      rw [div_div]
      congr 1
      ring

/-- The indexed local choice `B S = h^4` fits the same PPT mesh whenever
the remaining length is logarithmic in the comparison double logarithm.
The cutoff itself is a parameter, so no global normality transfer is used. -/
theorem ppt_local_normality_error_mesh {A : ℝ} (_hA : 0 < A) :
    ∀ᶠ t : ℝ in atTop, ∀ (h : ℕ) (S : ℝ),
      (h : ℝ) ≤ A*Real.log t → 0 ≤ B S → B S ≤ (h : ℝ)^4 →
      Real.sqrt (B S/t) ≤ (Real.log t)^5/Real.sqrt t := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 (A^2)))] with t ht
  intro h S hdim hBS hcutoff
  have hlog1 : 1 ≤ Real.log t := (le_max_left _ _).trans ht
  have hAlog : A^2 ≤ Real.log t := (le_max_right _ _).trans ht
  have hsqrt : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hlog3 : A^2 ≤ (Real.log t)^3 := by
    apply hAlog.trans
    simpa only [pow_one] using
      (pow_le_pow_right₀ hlog1 (show 1 ≤ 3 by omega))
  have hdim2 : (h : ℝ)^2 ≤ A^2*(Real.log t)^2 := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg h) hdim 2
    convert hh using 1
    ring
  have hdim5 : (h : ℝ)^2 ≤ (Real.log t)^5 := by
    apply hdim2.trans
    calc
      A^2*(Real.log t)^2 ≤ (Real.log t)^3*(Real.log t)^2 :=
        mul_le_mul_of_nonneg_right hlog3 (sq_nonneg _)
      _ = _ := by ring
  have hroot : Real.sqrt (B S) ≤ (h : ℝ)^2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨sq_nonneg _, ?_⟩
    convert hcutoff using 1
    ring
  rw [Real.sqrt_div hBS]
  exact (div_le_div_of_nonneg_right hroot hsqrt).trans
    (div_le_div_of_nonneg_right hdim5 hsqrt)

/-- The fourth-power indexed normality height is below the terminal
two-thirds-power height throughout the same logarithmic length range. -/
theorem ppt_local_normality_height_bound {A : ℝ} (_hA : 0 < A) :
    ∀ᶠ t : ℝ in atTop, ∀ h : ℕ,
      (h : ℝ) ≤ A*Real.log t → (h : ℝ)^4 ≤ t^(2/3 : ℝ) := by
  have hlim : Tendsto (fun t : ℝ => A^4*((Real.log t)^4/t^(2/3 : ℝ)))
      atTop (𝓝 0) := by
    have hh : Tendsto (fun t : ℝ => (Real.log t)^4/t^(2/3 : ℝ))
        atTop (𝓝 0) := by
      simpa only [Real.rpow_natCast] using
        (isLittleO_log_rpow_rpow_atTop (4 : ℕ)
          (show (0 : ℝ) < 2/3 by norm_num)).tendsto_div_nhds_zero
    simpa only [mul_zero] using hh.const_mul (A^4)
  filter_upwards [hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℝ)] with t hsmall ht
  intro h hdim
  have hpow : (h : ℝ)^4 ≤ A^4*(Real.log t)^4 := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg h) hdim 4
    convert hh using 1
    ring
  apply hpow.trans
  have hden : 0 < t^(2/3 : ℝ) := Real.rpow_pos_of_pos ht _
  apply (div_le_one hden).mp
  convert hsmall.le using 1
  ring

/-- If `B S ≤ h^4` and the terminal cutoff has double logarithm at least
`t^(2/3)`, the literal Ford condition `S ≤ Y` follows. -/
theorem ppt_local_normality_terminal_cutoff {A : ℝ} (hA : 0 < A) :
    ∀ᶠ t : ℝ in atTop, ∀ (h : ℕ) (S Y : ℝ),
      (h : ℝ) ≤ A*Real.log t → 1 < S → 1 < Y →
      B S ≤ (h : ℝ)^4 → t^(2/3 : ℝ) ≤ B Y → S ≤ Y := by
  filter_upwards [ppt_local_normality_height_bound hA] with t ht
  intro h S Y hdim hS hY hBS hBY
  have hheight := (hBS.trans (ht h hdim)).trans hBY
  have hexp := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hheight)
  simpa only [B, Real.exp_log (Real.log_pos hS), Real.exp_log (Real.log_pos hY),
    Real.exp_log (zero_lt_one.trans hS), Real.exp_log (zero_lt_one.trans hY)] using hexp

end TotientAsymptotic

end

end OAI
