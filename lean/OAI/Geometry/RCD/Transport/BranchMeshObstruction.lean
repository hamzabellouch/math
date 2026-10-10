import OAI.Geometry.RCD.Transport.BranchEntropyDeficit
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # A fixed positive branch window contradicts the entropy mesh estimate -/

open Filter
open scoped Topology
namespace RegularPointCoordinates

theorem exists_branch_mesh_obstruction {T S c C A B : ℝ}
    (hT : 0 < T) (hS : S < 1) (hTS : T < S) (hc : 0 < c) (hC : 0 < C) (hA : 0 ≤ A) :
    ∃ N : ℕ, 0 < N ∧ ∀ s m : ℝ, T ≤ s → s ≤ S → c*((S-T)/(N:ℝ)) ≤ m →
      ¬ s*(1-s)*Real.log 2 ≤ ((S-T)/(N:ℝ))*(Real.log (2*C/m)-B+A*s*(1-s)) := by
  have hL : 0 < T*(1-S)*Real.log 2 :=
    mul_pos (mul_pos hT (sub_pos.mpr hS)) (Real.log_pos (by norm_num))
  have hε : Tendsto (fun N : ℕ => (S-T)/(N:ℝ)) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_const_div_atTop_nhds_zero_nat (S-T),?_⟩
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact div_pos (sub_pos.mpr hTS) (Nat.cast_pos.mpr hN)
  have hsmall := hε.eventually (exists_small_branch_budget hL (Real.log (2*C/c)) B A)
  obtain ⟨N,hbudget,hN⟩ := (hsmall.and (eventually_gt_atTop 0)).exists
  refine ⟨N,hN,?_⟩
  intro s m hTs hsS hm hbad
  let ε := (S-T)/(N:ℝ)
  have hε0 : 0 < ε := div_pos (sub_pos.mpr hTS) (Nat.cast_pos.mpr hN)
  have hm0 : 0 < m := lt_of_lt_of_le (mul_pos hc hε0) hm
  have hs0 : 0 ≤ s := hT.le.trans hTs
  have hs1 : s ≤ 1 := hsS.trans hS.le
  have hlower : T*(1-S) ≤ s*(1-s) :=
    mul_le_mul hTs (sub_le_sub_left hsS 1) (sub_nonneg.mpr hS.le) hs0
  have hupper : s*(1-s) ≤ 1 := by nlinarith [sq_nonneg s]
  have hratio : 2*C/m ≤ 2*C/(c*ε) :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hC.le) (mul_pos hc hε0) hm
  have hlog : Real.log (2*C/m) ≤ Real.log (2*C/c)-Real.log ε := by
    have h := Real.log_le_log (div_pos (mul_pos (by norm_num) hC) hm0) hratio
    rw [Real.log_div (mul_pos (by norm_num) hC).ne' (mul_pos hc hε0).ne',
      Real.log_mul hc.ne' hε0.ne'] at h
    rw [Real.log_div (mul_pos (by norm_num) hC).ne' hc.ne']
    linarith
  have hAs : A*s*(1-s) ≤ A := by
    have h := mul_le_mul_of_nonneg_left hupper hA
    simpa only [mul_assoc,mul_one] using h
  have hbound : ε*(Real.log (2*C/m)-B+A*s*(1-s)) ≤
      ε*(Real.log (2*C/c)-Real.log ε-B+A) :=
    mul_le_mul_of_nonneg_left (by linarith) hε0.le
  have hstart := mul_le_mul_of_nonneg_right hlower (show 0 ≤ Real.log 2 from Real.log_nonneg (by norm_num))
  exact (not_lt_of_ge (hstart.trans (hbad.trans hbound))) hbudget

end RegularPointCoordinates

end OAI
