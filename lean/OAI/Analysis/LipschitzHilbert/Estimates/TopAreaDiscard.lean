import OAI.Analysis.LipschitzHilbert.Estimates.TopFamilyException
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Convert the exponential total-top-area exception to a small fraction
of the testing set, using only the manuscript's area and disparity bounds. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_top_area_factor (b H : ℝ) :
    ∀ᶠ L : ℝ in atTop, L^b*Real.exp (-6*L) ≤ (1/2)*L^(-H) := by
  have hsmall := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b+H) 6 (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    hsmall.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with L hL hsmall
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have h := mul_le_mul_of_nonneg_right hsmall.le (Real.rpow_nonneg hL0.le (-H))
  convert h using 1
  rw [mul_right_comm, ← Real.rpow_add hL0]
  congr 2
  ring

theorem top_area_discard_numeric (L b H N F S : ℝ)
    (hL : 0 < L) (hN : 0 ≤ N) (hF : 0 ≤ F)
    (hNupper : N ≤ Real.exp (2*L)) (harea : S ≤ L^b*N^2*F)
    (hsmall : L^b*Real.exp (-6*L) ≤ (1/2)*L^(-H)) :
    Real.exp (-10*L)*S ≤ (1/2)*L^(-H)*F := by
  have hNsq := pow_le_pow_left₀ hN hNupper 2
  have hExp : (Real.exp (2*L))^2 = Real.exp (4*L) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hExp] at hNsq
  calc
    _ ≤ Real.exp (-10*L)*(L^b*N^2*F) :=
      mul_le_mul_of_nonneg_left harea (Real.exp_pos _).le
    _ ≤ Real.exp (-10*L)*(L^b*Real.exp (4*L)*F) := by gcongr
    _ = (L^b*Real.exp (-6*L))*F := by
      rw [show Real.exp (-10*L)*(L^b*Real.exp (4*L)*F) =
        L^b*(Real.exp (-10*L)*Real.exp (4*L))*F by ring, ← Real.exp_add]
      rw [show -10*L+4*L = -6*L by ring]
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hF

end LipschitzHilbert

end

end OAI
