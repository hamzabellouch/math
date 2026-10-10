import Mathlib
import OAI.Combinatorics.TriangleRemoval.Stability.CavityWeight
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixWeight
import OAI.Combinatorics.TriangleRemoval.Process.WitnessMu

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
open Filter MeasureTheory
open scoped BigOperators Topology

lemma cavityWeight_lipschitz {D : ℝ} (hD : 0 ≤ D)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |cavityWeight D x - cavityWeight D y| ≤ (2*D)*|x-y| := by
  have hx1 : 1 ≤ 1+2*D*x := by nlinarith [mul_nonneg hD hx]
  have hy1 : 1 ≤ 1+2*D*y := by nlinarith [mul_nonneg hD hy]
  have hx0 : 0 < 1+2*D*x := by linarith
  have hy0 : 0 < 1+2*D*y := by linarith
  have he : cavityWeight D x - cavityWeight D y =
      (2*D*(y-x))/((1+2*D*x)*(1+2*D*y)) := by
    unfold cavityWeight
    field_simp
    ring
  rw [he,abs_div,abs_mul,abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD),
    abs_of_pos (mul_pos hx0 hy0),abs_sub_comm y x]
  have hden : 1 ≤ (1+2*D*x)*(1+2*D*y) := by nlinarith
  exact (div_le_iff₀ (mul_pos hx0 hy0)).mpr (by
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD)
      (abs_nonneg (x-y))) (sub_nonneg.mpr hden)])

lemma continuous_clipped_cavityWeight {D : ℝ} (hD : 0 ≤ D) :
    Continuous (fun t => cavityWeight D (unitTime t)) := by
  unfold cavityWeight
  apply Continuous.div continuous_const
    (continuous_const.add (continuous_const.mul continuous_unitTime))
  intro t
  change 1 + 2*D*unitTime t ≠ 0
  have ht := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD) (unitTime_nonneg t)
  linarith

lemma cavityWeight_integral {D : ℝ} (hD : 0 < D) :
    (∫ t in (0 : ℝ)..1, cavityWeight D (unitTime t)) = witnessMu D := by
  have hc : 2*D ≠ 0 := by positivity
  have he : (∫ t in (0 : ℝ)..1, cavityWeight D (unitTime t)) =
      ∫ t in (0 : ℝ)..1, 1/(1+(2*D)*t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    simp only [unitTime_of_mem ht,cavityWeight]
  rw [he,intervalIntegral.integral_comp_add_mul (fun x : ℝ => 1/x) hc 1]
  simp only [mul_zero,add_zero,mul_one,smul_eq_mul]
  rw [integral_one_div_of_pos (by norm_num : (0 : ℝ) < 1) (by linarith : 0 < 1+2*D)]
  simp only [div_one,witnessMu]
  ring

theorem gridWitnessWeight_error {D : ℝ} (hD : 0 < D) (N : ℕ) (hN : 0 < N) :
    |prefixWeight (fun j => (2/(N : ℝ))*cavityWeight D ((j : ℝ)/N)) N -
      2*witnessMu D| ≤ 4*D/N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh := uniform_grid_quadrature (fun t => cavityWeight D (unitTime t))
    (continuous_clipped_cavityWeight hD.le) (by positivity : (0 : ℝ) ≤ 2*D)
    (fun x hx y hy => by
      rw [unitTime_of_mem hx,unitTime_of_mem hy]
      exact cavityWeight_lipschitz hD.le hx.1 hy.1) N N hN le_rfl
  rw [div_self (ne_of_gt hNr),cavityWeight_integral hD] at hh
  have hs : (∑ j ∈ Finset.range N, cavityWeight D (unitTime ((j : ℝ)/N))) =
      ∑ j ∈ Finset.range N, cavityWeight D ((j : ℝ)/N) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [unitTime_of_mem ⟨by positivity,(div_le_one hNr).mpr (by exact_mod_cast (Finset.mem_range.mp hj).le)⟩]
  rw [hs,abs_sub_comm] at hh
  have he : prefixWeight (fun j => (2/(N : ℝ))*cavityWeight D ((j : ℝ)/N)) N -
      2*witnessMu D =
      2*((1/(N : ℝ))*(∑ j ∈ Finset.range N, cavityWeight D ((j : ℝ)/N)) - witnessMu D) := by
    unfold prefixWeight
    rw [← Finset.mul_sum]
    ring
  rw [he,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2*(2*D/N) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by ring

theorem gridWitnessWeight_tendsto {D : ℝ} (hD : 0 < D) :
    Tendsto (fun N : ℕ => prefixWeight
      (fun j => (2/((N+1 : ℕ) : ℝ))*cavityWeight D ((j : ℝ)/(N+1 : ℕ))) (N+1))
      atTop (𝓝 (2*witnessMu D)) := by
  have hz : Tendsto (fun N : ℕ => 4*D/((N+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := 4*D)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun N : ℕ => (1 : ℝ)/(N+1)) atTop (𝓝 0))
    simpa only [Nat.cast_add,Nat.cast_one,mul_zero,div_eq_mul_inv,one_mul] using h
  have hl : Tendsto (fun N : ℕ => 2*witnessMu D - 4*D/((N+1 : ℕ) : ℝ))
      atTop (𝓝 (2*witnessMu D)) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := 2*witnessMu D)).sub hz
  have hu : Tendsto (fun N : ℕ => 2*witnessMu D + 4*D/((N+1 : ℕ) : ℝ))
      atTop (𝓝 (2*witnessMu D)) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := 2*witnessMu D)).add hz
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
  · intro N
    have h := (abs_le.mp (gridWitnessWeight_error hD (N+1) (by omega))).1
    linarith
  · intro N
    have h := (abs_le.mp (gridWitnessWeight_error hD (N+1) (by omega))).2
    linarith

end SharpTerminalLeave

end

end OAI
