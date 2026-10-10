import OAI.NumberTheory.TotientAsymptotic.BootstrapNormalityDecay

namespace OAI

/-! The square-divisor cutoff is much larger than every fixed logarithmic power. -/
noncomputable section
namespace TotientAsymptotic

lemma exp_quadratic_lower {u : ℝ} (hu : 0 ≤ u) : u^2/4 ≤ Real.exp u := by
  have he := Real.add_one_le_exp (u/2)
  have hhalf : 0 ≤ u/2 := by linarith
  have hs : (u/2)^2 ≤ (Real.exp (u/2))^2 :=
    pow_le_pow_left₀ hhalf (by linarith) 2
  have hid : (Real.exp (u/2))^2=Real.exp u := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [hid] at hs
  nlinarith only [hs]

lemma bootstrap_square_cutoff {b : ℝ} (hb : 1000000000000000000 ≤ b) :
    Real.exp (3*b) ≤ (loglogCutoff (bootstrapBottom b):ℝ) := by
  let L := bootstrapBottom b
  let S := loglogCutoff L
  have hL : 2 ≤ L := Nat.le_floor (show (2:ℝ) ≤ b/100000000 by linarith)
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hs := loglogCutoff_bounds hLR
  have hS4 := loglogCutoff_ge_four hLR
  have hS0 : (0:ℝ) < S := by exact_mod_cast (show 0 < S by omega)
  have hlogS : 0 < Real.log S := Real.log_pos (by exact_mod_cast (show 1 < S by omega))
  have hBl : b/200000000 ≤ B S := by
    have hh : b/100000000-1 < (L:ℝ) := Nat.sub_one_lt_floor (b/100000000)
    linarith only [hh,hs.2.1,hb]
  have hB0 : 0 ≤ B S := by linarith
  have hsquare : 3*b ≤ (B S)^2/4 := by
    have hh := pow_le_pow_left₀ (show (0:ℝ) ≤ b/200000000 by linarith) hBl 2
    have hb2 : 1000000000000000000*b ≤ b^2 := by nlinarith only [hb]
    nlinarith only [hh,hb2]
  have hlog : 3*b ≤ Real.log S := by
    have hh := hsquare.trans (exp_quadratic_lower hB0)
    rwa [B,Real.exp_log hlogS] at hh
  exact (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log hS0)

end TotientAsymptotic

end

end OAI
