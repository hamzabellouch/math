import Mathlib
import OAI.Combinatorics.TriangleRemoval.Stability.CavityWeightLipschitz

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

lemma continuous_cavityWeight_clip {D : ℝ} (hD : 0 ≤ D) :
    Continuous (fun t => cavityWeight D (unitTime t)) := by
  unfold cavityWeight
  apply continuous_const.div
    (continuous_const.add ((continuous_const.mul continuous_const).mul continuous_unitTime))
  intro t
  have ht := unitTime_nonneg t
  apply ne_of_gt
  change 0 < 1+2*D*unitTime t
  have hh : 0 ≤ 2*D*unitTime t := mul_nonneg (mul_nonneg (by norm_num) hD) ht
  linarith

lemma cavityWeight_lipschitz_cell {D x y : ℝ} (hD : 0 ≤ D)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |cavityWeight D x - cavityWeight D y| ≤ (2*D)*|x-y| := by
  have ha : 1 ≤ 1+2*D*x := le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hD) hx)
  have hb : 1 ≤ 1+2*D*y := le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hD) hy)
  have ha0 : 0 < 1+2*D*x := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < 1+2*D*y := lt_of_lt_of_le zero_lt_one hb
  have hid : 1/(1+2*D*x)-1/(1+2*D*y) =
      (2*D*(y-x))/((1+2*D*x)*(1+2*D*y)) := by
    field_simp
    ring
  unfold cavityWeight
  rw [hid,abs_div,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*D),
    abs_of_pos (mul_pos ha0 hb0),abs_sub_comm y x]
  exact div_le_self (by positivity) (one_le_mul_of_one_le_of_one_le ha hb)

theorem grid_prefixWeight_tendsto {D : ℝ} (hD : 0 < D) :
    Tendsto (fun j : ℕ =>
      prefixWeight (fun t => (2/((j+1 : ℕ) : ℝ))*cavityWeight D ((t : ℝ)/(j+1 : ℕ))) (j+1))
      atTop (𝓝 (2*witnessMu D)) := by
  have hquad (j : ℕ) :
      |prefixWeight (fun t => (2/((j+1 : ℕ) : ℝ))*cavityWeight D ((t : ℝ)/(j+1 : ℕ))) (j+1) -
        2*witnessMu D| ≤ 4*D/((j+1 : ℕ) : ℝ) := by
    have hN : 0 < j+1 := Nat.succ_pos j
    have hNr : (0 : ℝ) < (j+1 : ℕ) := by exact_mod_cast hN
    have hh := uniform_grid_quadrature (fun t => cavityWeight D (unitTime t))
      (continuous_cavityWeight_clip hD.le) (show 0 ≤ 2*D by positivity)
      (fun x hx y hy => by
        rw [unitTime_of_mem hx,unitTime_of_mem hy]
        exact cavityWeight_lipschitz_cell hD.le hx.1 hy.1) (j+1) (j+1) hN le_rfl
    rw [div_self (ne_of_gt hNr),cavityWeight_integral hD] at hh
    have heq : (∑ t ∈ Finset.range (j+1), cavityWeight D (unitTime ((t : ℝ)/(j+1 : ℕ)))) =
        ∑ t ∈ Finset.range (j+1), cavityWeight D ((t : ℝ)/(j+1 : ℕ)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [unitTime_of_mem ⟨by positivity,(div_le_one hNr).mpr
        (by exact_mod_cast (Finset.mem_range.mp ht).le)⟩]
    rw [heq] at hh
    have hb := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)
    calc
      _ = 2*|witnessMu D - (1/((j+1 : ℕ) : ℝ))*
          ∑ t ∈ Finset.range (j+1), cavityWeight D ((t : ℝ)/(j+1 : ℕ))| := by
        unfold prefixWeight
        rw [← Finset.mul_sum]
        rw [show (2 : ℝ) = |(2 : ℝ)| by norm_num, ← abs_mul, ← abs_neg]
        congr 1
        ring
      _ ≤ _ := by
        calc
          _ ≤ 2*(2*D/((j+1 : ℕ) : ℝ)) := hb
          _ = _ := by ring
  have hden : Tendsto (fun j : ℕ => (4*D)/((j+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have hh := tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (4*D)
    simpa only [Nat.cast_add,Nat.cast_one,mul_comm,one_div,div_eq_mul_inv,one_mul,zero_mul] using hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (fun j => by rw [Real.norm_eq_abs]; exact hquad j) hden

lemma collision_exponential_identity {D : ℝ} (hD : 0 < D) :
    (1+2*D)^3*Real.exp (45*D*(2*witnessMu D)) = (1+2*D)^48 := by
  have he : 45*D*(2*witnessMu D) = 45*Real.log (1+2*D) := by
    unfold witnessMu
    field_simp
  rw [he,show (45 : ℝ) = (45 : ℕ) by norm_num,Real.exp_nat_mul,
    Real.exp_log (by linarith : 0 < 1+2*D),← pow_add]

lemma collision_power_48_bound {D : ℝ} (hD : 1 ≤ D) :
    (1+2*D)^48/D^50 ≤ (3 : ℝ)^48/D^2 := by
  have hpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hh := div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : 0 ≤ 1+2*D) (by linarith : 1+2*D ≤ 3*D) 48)
    (by positivity : 0 ≤ D^50)
  apply hh.trans_eq
  rw [mul_pow,show 50 = 48+2 by norm_num,pow_add]
  field_simp

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
