import OAI.NumberTheory.TotientAsymptotic.SieveCutoff

namespace OAI

/-! The existing small-power cutoff also supports sieve dimension three. -/
noncomputable section
namespace TotientAsymptotic

lemma tripleSieveCutoff_three {L : ℝ} (hL : 512*Real.log 4 ≤ L) :
    3 ≤ shiftedPrimeCutoff L := by
  have hc : 0 < Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have hz := shiftedPrimeCutoff_bounds hL
  have hlow : (2:ℝ) ≤ L/(256*Real.log 4) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hp : (0:ℝ) < shiftedPrimeCutoff L := by exact_mod_cast (show 0 < shiftedPrimeCutoff L by omega)
  have hh := Real.log_le_sub_one_of_pos hp
  have hthree : (3:ℝ) ≤ shiftedPrimeCutoff L := by linarith [hz.2.1]
  exact_mod_cast hthree

lemma tripleSieveCutoff_scale {L : ℝ} (hL : 512*Real.log 4 ≤ L) :
    12*Real.log 4*(2+Real.log (shiftedPrimeCutoff L)) ≤ Real.log (Real.exp (L/4)) := by
  have hc : 0 < Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have hh := (shiftedPrimeCutoff_bounds hL).2.2.1
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 12*Real.log 4 by positivity)
  have he : 12*Real.log 4*(L/(128*Real.log 4))=3*L/32 := by field_simp; ring
  rw [he] at hm
  rw [Real.log_exp]
  nlinarith

lemma tripleSieveCutoff_error {L : ℝ} (hL : 512*Real.log 4 ≤ L) :
    (shiftedPrimeCutoff L:ℝ)+2*(Real.exp (L/4))^3 ≤ 1152*Real.exp L/L^3 := by
  have hc : 0 < Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have hL0 : 0 < L := by nlinarith
  have he : (Real.exp (L/4))^3 = Real.exp (3*L/4) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hcube := Real.pow_div_factorial_le_exp (L/4) (show 0 ≤ L/4 by positivity) 3
  norm_num only [Nat.factorial] at hcube
  have hsmall : L^3 ≤ 384*Real.exp (L/4) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos (3*L/4)).le
  have hsum : Real.exp (L/4)*Real.exp (3*L/4)=Real.exp L := by
    rw [← Real.exp_add]; congr 1; ring
  have hbound : 3*Real.exp (3*L/4) ≤ 1152*Real.exp L/L^3 := by
    apply (le_div_iff₀ (pow_pos hL0 3)).mpr
    rw [mul_assoc,hsum] at hm
    nlinarith
  rw [he]
  exact (by linarith [(shiftedPrimeCutoff_bounds hL).2.2.2] :
    (shiftedPrimeCutoff L:ℝ)+2*Real.exp (3*L/4) ≤ 3*Real.exp (3*L/4)).trans hbound

end TotientAsymptotic

end

end OAI
