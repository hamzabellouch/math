import Mathlib

namespace OAI

noncomputable section
open Filter Asymptotics

namespace BinaryCoordinateSweeps.Sparse

lemma nat_pow_le_exp_of_le {x A : ℝ} (hx : 0≤x) (h : x≤Real.exp A) (n : ℕ) :
    x^n≤Real.exp ((n:ℝ)*A) := by
  simpa only [←Real.exp_nat_mul] using pow_le_pow_left₀ hx h n

lemma log_le_small_rpow_eventually {ε : ℝ} (hε : 0<ε) : ∀ᶠ s : ℕ in atTop,
    Real.log (s:ℝ)≤(s:ℝ)^ε := by
  have hh := (isLittleO_log_rpow_rpow_atTop (1:ℝ) hε).bound (by norm_num : (0:ℝ)<1)
  have hc : Tendsto (fun s : ℕ => (s:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hc.eventually hh,eventually_ge_atTop (1:ℕ)] with s hs hs1
  have hl : 0≤Real.log (s:ℝ) := Real.log_nonneg (by exact_mod_cast hs1)
  simpa only [Real.rpow_one,Real.norm_of_nonneg hl,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg s) ε),one_mul] using hs

lemma many_hs_scalar (b h k : ℕ) {L x : ℝ} (hb : 1≤b)
    (hh : (h:ℝ)≤100000*k) (hL : 4000000000*(b:ℝ)≤L)
    (hx0 : 0≤x) (hx : x≤Real.exp (-L/4000)) :
    ((2:ℝ)^k*Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b))^2 *
      ((2:ℝ)^k*x^((k+1)/2)) ≤ Real.exp (-(k:ℝ)*L/16000) := by
  have hL0 : 0≤L := (by positivity : (0:ℝ)≤4000000000*b).trans hL
  have hbk : (1:ℝ)≤b := by exact_mod_cast hb
  have hkt : (k:ℝ)≤2*(((k+1)/2:ℕ):ℝ) := by exact_mod_cast (show k≤2*((k+1)/2) from by omega)
  have hal : x^((k+1)/2)≤Real.exp (-(k:ℝ)*L/8000) := by
    apply (nat_pow_le_exp_of_le hx0 hx _).trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hkt hL0]
  have hlog2 : Real.log 2≤2 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)).trans (by norm_num)
  have hlog4 : Real.log 4≤4 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)).trans (by norm_num)
  have hp (n : ℕ) : (2:ℝ)^n=Real.exp ((n:ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  calc
    _ ≤ ((2:ℝ)^k*Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b))^2 *
        ((2:ℝ)^k*Real.exp (-(k:ℝ)*L/8000)) := by gcongr
    _ = Real.exp (3*(k:ℝ)*Real.log 2+2*((b:ℝ)*(h+k)+Real.log 4*k*b)-(k:ℝ)*L/8000) := by
      simp only [hp,←Real.exp_add,←Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh' := mul_le_mul_of_nonneg_left hh (show (0:ℝ)≤b by positivity)
      have h2 := mul_le_mul_of_nonneg_left hlog2 (show (0:ℝ)≤k by positivity)
      have h4 := mul_le_mul_of_nonneg_right hlog4 (show (0:ℝ)≤k*b by positivity)
      have hkb := mul_le_mul_of_nonneg_left hbk (show (0:ℝ)≤k by positivity)
      have hLc := mul_le_mul_of_nonneg_right hL (show (0:ℝ)≤k by positivity)
      nlinarith

end BinaryCoordinateSweeps.Sparse

end

end OAI
