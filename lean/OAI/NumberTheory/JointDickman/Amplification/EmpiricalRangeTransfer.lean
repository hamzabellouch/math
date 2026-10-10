import OAI.NumberTheory.JointDickman.Amplification.BinPrefixMeans
import OAI.NumberTheory.JointDickman.Basic

namespace OAI

/-! # Passing from range averages to the manuscript's interval 2 ≤ n ≤ N -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem bounded_nat_div_tendsto_zero (f : ℕ → ℂ) {C : ℝ} (_hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C) : Tendsto (fun n => f n/(n : ℂ)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (g := fun n : ℕ => C/(n : ℝ))
  · intro n
    rw [norm_div,Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (hf n) (Nat.cast_nonneg n)
  · exact tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) C

theorem sum_Icc_two_eq_range {N : ℕ} (hN : 1 ≤ N) (f : ℕ → ℂ) :
    (∑ n ∈ Icc 2 N, f n) = (∑ n ∈ range N, f n)+f N-f 0-f 1 := by
  have hset : insert 1 (Icc 2 N) = Ioc 0 N := by
    ext n
    simp only [mem_insert,mem_Icc,mem_Ioc]
    omega
  have hh := sum_Ioc_zero_eq_range_add f N
  rw [← hset,sum_insert (by simp)] at hh
  linear_combination hh

theorem empirical_limit_of_range_limit (P : ℕ → ℕ → Prop) {L : ℂ}
    (h : Tendsto (fun N => (∑ n ∈ range N, if P N n then (1 : ℂ) else 0)/(N : ℂ)) atTop (𝓝 L)) :
    Tendsto (fun N => (empiricalCount (P N) N : ℂ)/(N : ℂ)) atTop (𝓝 L) := by
  let f := fun N n => if P N n then (1 : ℂ) else 0
  have hb (g : ℕ → ℕ) : Tendsto (fun N => f N (g N)/(N : ℂ)) atTop (𝓝 0) := by
    apply bounded_nat_div_tendsto_zero _ (by norm_num : (0 : ℝ) ≤ 1)
    intro N
    dsimp [f]
    split_ifs <;> norm_num
  have hh := ((h.add (hb id)).sub (hb (fun _ => 0))).sub (hb (fun _ => 1))
  simp only [add_zero,sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have he := sum_Icc_two_eq_range hN (f N)
  have hc : (empiricalCount (P N) N : ℂ) = ∑ n ∈ Icc 2 N, f N n := by
    simp [empiricalCount,f]
  rw [hc,he]
  dsimp only [f,id_eq]
  ring

end JointDickman

end OAI
