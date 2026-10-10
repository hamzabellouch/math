import OAI.NumberTheory.JointDickman.Analysis.MellinApplicationScales

namespace OAI

/-! # The canonical error on the short-window frequency range -/
namespace JointDickman
open TwoPointCorrelations

lemma canonical_cost_le_window {N : ℕ} {H T : ℝ} (hN : 0 < N)
    (hH : 1 ≤ H) (_hT : 0 ≤ T) (hTH : T ≤ (N:ℝ)/H) :
    2816*Real.exp 1*(T/N+1)*(8/(mellinFirstPrime H)+4/(mellinResolution H))+
      1024*Real.exp 2*(T*mellinLastPrime H/N+1)*(mellinResolution H)⁻¹+
      2*(T/N+1)/(mellinFirstPrime H) ≤ mellinWindowCost H := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hh : 0<H := by linarith
  have hp : 0 ≤ mellinFirstPrime H := Real.rpow_nonneg (Real.log_nonneg hH) _
  have hq : 0 ≤ mellinLastPrime H := Real.rpow_nonneg hh.le _
  have hr : 0 < mellinResolution H := mrtBaseResolution_pos _ _ _
  have ht : T/(N:ℝ) ≤ H⁻¹ := by
    calc
      _ ≤ ((N:ℝ)/H)/N := div_le_div_of_nonneg_right hTH hn.le
      _ = _ := by field_simp
  have htq : T*mellinLastPrime H/N ≤ mellinLastPrime H/H := by
    calc
      _ = (T/N)*mellinLastPrime H := by ring
      _ ≤ H⁻¹*mellinLastPrime H := mul_le_mul_of_nonneg_right ht hq
      _ = _ := by ring
  unfold mellinWindowCost
  gcongr
  change _ ≤ 1024*Real.exp 2*(mellinLastPrime H/H+1)*(mellinResolution H)⁻¹
  gcongr

end JointDickman

end OAI
