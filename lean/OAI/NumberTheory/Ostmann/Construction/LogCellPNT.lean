import OAI.NumberTheory.Ostmann.Reuse.PrimeGaps

namespace OAI

open Filter Asymptotics
open scoped Topology
namespace Ostmann.Construction

theorem tendsto_psi_nat_ratio :
    Tendsto (fun n : ℕ => Chebyshev.psi n/(n:ℝ)) atTop (𝓝 1) := by
  obtain ⟨M,hM,hbound⟩ := LargePrimeGaps.quantitative_PNT 1 zero_lt_one
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun n : ℕ => M*(Real.log (n:ℝ))^(-(1:ℝ))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ((tendsto_rpow_neg_atTop zero_lt_one).comp hlog)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hbound, eventually_gt_atTop 0, (tendsto_order.mp hzero).2 ε hε]
    with n hn hn0 hεn
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hb : |Chebyshev.psi n-(n:ℝ)| ≤ M*(n:ℝ)*(Real.log (n:ℝ))^(-(1:ℝ)) := by
    simpa only [Chebyshev.psi, Nat.floor_natCast] using hn
  rw [Real.dist_eq]
  have heq : Chebyshev.psi n/(n:ℝ)-1 = (Chebyshev.psi n-(n:ℝ))/(n:ℝ) := by
    field_simp
  rw [heq, abs_div, abs_of_pos hnR]
  apply lt_of_le_of_lt _ hεn
  apply (div_le_iff₀ hnR).mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hb

theorem tendsto_psi_ratio :
    Tendsto (fun x : ℝ => Chebyshev.psi x/x) atTop (𝓝 1) := by
  have hprod := (tendsto_psi_nat_ratio.comp (tendsto_nat_floor_atTop (α := ℝ))).mul
    (tendsto_nat_floor_div_atTop (R := ℝ))
  simp only [one_mul] at hprod
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  have hf : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr (by simpa using hx)
  have hf0 : (⌊x⌋₊:ℝ) ≠ 0 := by exact_mod_cast (by omega : ⌊x⌋₊ ≠ 0)
  rw [Chebyshev.psi_eq_psi_coe_floor x]
  dsimp only [Function.comp_apply]
  field_simp

theorem tendsto_theta_ratio :
    Tendsto (fun x : ℝ => Chebyshev.theta x/x) atTop (𝓝 1) := by
  have hsqrt : Tendsto (fun x : ℝ => Real.sqrt x/x) atTop (𝓝 0) := by
    apply (tendsto_rpow_neg_atTop (by norm_num : 0 < (1/2:ℝ))).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    symm
    calc
      Real.sqrt x/x = x^(1/2:ℝ)/x^(1:ℝ) := by rw [Real.sqrt_eq_rpow, Real.rpow_one]
      _ = x^((1/2:ℝ)-1) := (Real.rpow_sub hx _ _).symm
      _ = x^(-(1/2:ℝ)) := by congr 1; norm_num
  have hs : (fun x : ℝ => Real.sqrt x) =o[atTop] (fun x : ℝ => x) :=
    (isLittleO_iff_tendsto (fun x hx => by simp [hx])).mpr hsqrt
  have hzero := (Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hs).tendsto_div_nhds_zero
  have h := tendsto_psi_ratio.sub hzero
  simp only [sub_zero] at h
  convert h using 1
  funext x
  dsimp
  ring

end Ostmann.Construction

end OAI
