import OAI.NumberTheory.TotientAsymptotic.CoordinateCutoffs
import OAI.NumberTheory.TotientAsymptotic.BootstrapNormalityDecay

namespace OAI

/-! Decay of the square-divisor and normality errors at the chosen cutoff. -/
noncomputable section
namespace TotientAsymptotic

lemma loglog_cutoff_reciprocal {L : ℕ} {b : ℝ} (hL : 3 ≤ L)
    (hsize : 3*b ≤ Real.exp ((L:ℝ)-1)) :
    (1:ℝ)/(loglogCutoff L+1:ℕ) ≤ Real.exp (-3*b) := by
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hc := loglogCutoff_bounds hLR
  have hS0 : (0:ℝ) < loglogCutoff L := by exact_mod_cast (show 0 < loglogCutoff L by omega)
  have hlog : 0 < Real.log (loglogCutoff L) := Real.log_pos (by
    exact_mod_cast (show 1 < loglogCutoff L by omega))
  have hexp := Real.exp_le_exp.mpr hc.2.1
  rw [B,Real.exp_log hlog] at hexp
  have hlarge := Real.exp_le_exp.mpr (hsize.trans hexp)
  rw [Real.exp_log hS0] at hlarge
  calc
    _ ≤ (1:ℝ)/Real.exp (3*b) := by
      apply one_div_le_one_div_of_le (Real.exp_pos _)
      push_cast
      linarith
    _ = _ := by rw [one_div,← Real.exp_neg]; congr 1; ring

lemma loglog_cutoff_normality_factor {L : ℕ} (hL : 3 ≤ L) :
    (Real.log (loglogCutoff L))^(-1/6:ℝ) ≤ Real.exp (-((L:ℝ)-1)/6) := by
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hc := loglogCutoff_bounds hLR
  have hlog : 0 < Real.log (loglogCutoff L) := Real.log_pos (by
    exact_mod_cast (show 1 < loglogCutoff L by omega))
  rw [Real.rpow_def_of_pos hlog]
  apply Real.exp_le_exp.mpr
  change B (loglogCutoff L)*(-1/6:ℝ) ≤ -((L:ℝ)-1)/6
  linarith [hc.2.1]

lemma coordinate_normality_factor {b ω : ℝ} {k : ℕ}
    (hb : 0 ≤ b) (hω : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hlarge : 4 ≤ ω^2*b/(1000000*((k:ℝ)+2)^6)) :
    (Real.log (loglogCutoff (coordinateBottom b ω k)))^(-1/6:ℝ) ≤
      Real.exp (1/3:ℝ)*Real.exp (-ω^2*b/(6000000*((k:ℝ)+2)^6)) := by
  have hc := coordinate_bottom_bounds hb hω hω1 hlarge
  apply (loglog_cutoff_normality_factor hc.1).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := hc.2.2.2
  have he : -ω^2*b/(6000000*((k:ℝ)+2)^6) =
      -(ω^2*b/(1000000*((k:ℝ)+2)^6))/6 := by field_simp; ring
  rw [he]
  linarith

end TotientAsymptotic

end

end OAI
