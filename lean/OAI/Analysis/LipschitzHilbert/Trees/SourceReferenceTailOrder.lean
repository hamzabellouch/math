import OAI.Analysis.LipschitzHilbert.Estimates.MomentSuperlevel
import Mathlib.Order.Filter.AtTopBot.Basic

namespace OAI

/-! A moment order proportional to the source parameter gives any fixed
exponential tail while its threshold loses only two polynomial powers. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_source_reference_tail_order (J : ℝ) (hJ : 0 ≤ J) :
    ∀ᶠ L : ℝ in atTop, ∃ n : ℕ, 1 ≤ n ∧ 4*(n:ℝ) ≤ L^2 ∧
      (1/4:ℝ)^n ≤ Real.exp (-J*L) := by
  let d := J/Real.log 4+1
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hd : 0 < d := by dsimp [d]; positivity
  filter_upwards [eventually_ge_atTop (max 1 (4*d+4))] with L hlarge
  have hL : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hLd : 4*d+4 ≤ L := (le_max_right _ _).trans hlarge
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  let n := ⌈d*L⌉₊
  have hlo : d*L ≤ (n:ℝ) := Nat.le_ceil _
  have hhi : (n:ℝ) ≤ d*L+1 := (Nat.ceil_lt_add_one (mul_pos hd hL0).le).le
  refine ⟨n,Nat.ceil_pos.mpr (mul_pos hd hL0),?_,?_⟩
  · nlinarith
  · rw [quarter_pow_exp]
    apply Real.exp_le_exp.mpr
    have hmult := mul_le_mul_of_nonneg_left hlo hlog.le
    have heq : Real.log 4*(d*L) = (J+Real.log 4)*L := by
      dsimp [d]
      field_simp [hlog.ne']
    rw [heq] at hmult
    nlinarith

end LipschitzHilbert

end

end OAI
