import Mathlib
import OAI.Combinatorics.UniformKServer.StarActualJumps
import OAI.Combinatorics.UniformKServer.StarCoarseBudgets

namespace OAI

                                          
section

/-! Summed jumps and fine endpoints under one law, with a single logarithm. -/
noncomputable section
namespace UniformKServer.StarIntegratedJumps
open Finset StarRanks StarSchedules RankTracking CoarseData StarLocalCharges StarEnergy
open StarActualJumps StarCoarseBudgets
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem slope_bound (k : ℕ) : sideSlope k ≤ (10:ℝ)^18*EpochAlpha.ell k := by
  have h := EpochAlpha.ell_one k
  norm_num [sideSlope,StarConstants.cw]
  linarith

theorem fine_endpoints (d : Data Ω ι k) (H : ℕ) :
    integral d H (endpoints d (StarConstants.rho/EpochAlpha.ell k)) ≤
      (10:ℝ)^20*EpochAlpha.ell k*energy d H := by
  have h := endpoint_budget d (StarCaps.tolerance k).1 (StarCaps.tolerance k).2 H
  have he : 160/(StarConstants.rho/EpochAlpha.ell k)=(160/StarConstants.rho)*EpochAlpha.ell k := by
    rw [div_div_eq_mul_div]; ring
  rw [he] at h
  norm_num [StarConstants.rho] at h ⊢
  have hp := mul_nonneg (le_trans (by norm_num : (0:ℝ) ≤ 1) (EpochAlpha.ell_one k)) (energy_nonneg d H)
  nlinarith only [h,hp]

theorem alpha_abs_jump (d : Data Ω ι k) (H : ℕ) :
    integral d H (fun t ω => |AlphaFiniteLedger.jump (StarOutputData.alphaData d) t ω|) ≤
      (10:ℝ)^55*EpochAlpha.ell k*energy d H := by
  have h := average_mono (fun ω => (d.positive ω).le) (alpha_jump d H)
  simp only [average_add,average_mul,average_range_sum] at h
  change integral d H (fun t ω => |AlphaFiniteLedger.jump (StarOutputData.alphaData d) t ω|) ≤
    4100000*alphaScale k*integral d H _+4400*alphaScale k*integral d H _ at h
  have hs := mul_le_mul_of_nonneg_left (size_budget d H) (scale_nonneg k)
  have hp := mul_le_mul_of_nonneg_left (parent_budget d H) (scale_nonneg k)
  have hn := mul_nonneg (scale_nonneg k) (energy_nonneg d H)
  norm_num [alphaScale,StarConstants.multiplier] at h hs hp hn
  nlinarith only [h,hs,hp,hn]

theorem side_abs_jump (d : Data Ω ι k) (hk : 1 ≤ k) (H : ℕ) :
    integral d H (fun t ω => |SideFiniteLedger.jump (StarOutputData.sideData d hk) t ω|) ≤
      (10:ℝ)^55*EpochAlpha.ell k*energy d H := by
  have h := average_mono (fun ω => (d.positive ω).le) (side_jump d hk H)
  simp only [average_add,average_mul,average_range_sum] at h
  change integral d H (fun t ω => |SideFiniteLedger.jump (StarOutputData.sideData d hk) t ω|) ≤
    97920*sideSlope k*integral d H _+480*sideSlope k*integral d H _ at h
  have hs := mul_le_mul_of_nonneg_left (size_budget d H) (slope_nonneg k)
  have hp := mul_le_mul_of_nonneg_left (parent_budget d H) (slope_nonneg k)
  have hb := mul_le_mul_of_nonneg_right (slope_bound k) (energy_nonneg d H)
  have hn := mul_nonneg (le_trans (by norm_num : (0:ℝ) ≤ 1) (EpochAlpha.ell_one k)) (energy_nonneg d H)
  nlinarith only [h,hs,hp,hb,hn]

theorem alpha_jump_budget (d : Data Ω ι k) (H : ℕ) :
    integral d H (AlphaFiniteLedger.jump (StarOutputData.alphaData d)) ≤
      (10:ℝ)^55*EpochAlpha.ell k*energy d H :=
  (integral_mono d H (fun _ _ => le_abs_self _)).trans (alpha_abs_jump d H)

theorem side_jump_budget (d : Data Ω ι k) (hk : 1 ≤ k) (H : ℕ) :
    integral d H (SideFiniteLedger.jump (StarOutputData.sideData d hk)) ≤
      (10:ℝ)^55*EpochAlpha.ell k*energy d H :=
  (integral_mono d H (fun _ _ => le_abs_self _)).trans (side_abs_jump d hk H)

end UniformKServer.StarIntegratedJumps

end


end

end OAI
