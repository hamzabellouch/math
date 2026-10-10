import OAI.NumberTheory.TotientAsymptotic.SieveEulerProduct

namespace OAI

/-! Explicit small-power cutoffs for the two-linear-form sieve. -/
noncomputable section
namespace TotientAsymptotic

def shiftedPrimeCutoff (L : ℝ) : ℕ := ⌊Real.exp (L/(128*Real.log 4))⌋₊

lemma shiftedPrimeCutoff_bounds {L : ℝ} (hL : 512*Real.log 4 ≤ L) :
    2 ≤ shiftedPrimeCutoff L ∧
    L/(256*Real.log 4) ≤ Real.log (shiftedPrimeCutoff L) ∧
    Real.log (shiftedPrimeCutoff L) ≤ L/(128*Real.log 4) ∧
    (shiftedPrimeCutoff L:ℝ) ≤ Real.exp (3*L/4) := by
  have hc : 1 ≤ Real.log 4 := by
    have h := Real.log_two_gt_d9
    have he : Real.log (4:ℝ) = 2*Real.log 2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
    linarith
  have hL0 : 0<L := by nlinarith
  have hd : 0<128*Real.log 4 := by positivity
  have hu : 4 ≤ L/(128*Real.log 4) := (le_div_iff₀ hd).mpr (by nlinarith)
  have he2 : (2:ℝ) ≤ Real.exp (L/(128*Real.log 4)) := by
    have hh := Real.add_one_le_exp (L/(128*Real.log 4))
    linarith
  have hz : 2 ≤ shiftedPrimeCutoff L := (Nat.le_floor_iff (by positivity)).mpr he2
  have hz0 : (0:ℝ)<shiftedPrimeCutoff L := by exact_mod_cast (show 0<shiftedPrimeCutoff L by omega)
  have hfloor := Nat.sub_one_lt_floor (Real.exp (L/(128*Real.log 4)))
  have hhalf : Real.exp (L/(128*Real.log 4))/2 ≤ (shiftedPrimeCutoff L:ℝ) := by
    dsimp [shiftedPrimeCutoff]
    linarith
  have hlower := Real.log_le_log (by positivity) hhalf
  rw [Real.log_div (Real.exp_pos _).ne' (by norm_num),Real.log_exp] at hlower
  have hlog2 : Real.log (2:ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at this
    exact this
  have hfrac : L/(256*Real.log 4) = (L/(128*Real.log 4))/2 := by ring
  refine ⟨hz,?_,?_,?_⟩
  · rw [hfrac]
    linarith
  · have hh := Real.log_le_log hz0 (Nat.floor_le (Real.exp_pos _).le)
    simpa only [Real.log_exp] using hh
  · apply (Nat.floor_le (Real.exp_pos _).le).trans
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ hd).mpr
    nlinarith

lemma shiftedPrimeCutoff_scale {L : ℝ} (hL : 512*Real.log 4 ≤ L) :
    8*Real.log 4*(2+Real.log (shiftedPrimeCutoff L)) ≤
      Real.log (Real.exp (L/4)) := by
  have hc : 0<Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have hh := (shiftedPrimeCutoff_bounds hL).2.2.1
  have hm := mul_le_mul_of_nonneg_left hh (show 0≤8*Real.log 4 by positivity)
  have he : 8*Real.log 4*(L/(128*Real.log 4))=L/16 := by field_simp; ring
  rw [he] at hm
  rw [Real.log_exp]
  nlinarith

lemma shiftedPrimeCutoff_error {L : ℝ} (hL : 512*Real.log 4 ≤ L) :
    (shiftedPrimeCutoff L:ℝ)+2*(Real.exp (L/4))^3 ≤
      96*Real.exp L/L^2 := by
  have hc : 0<Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have hL0 : 0<L := by nlinarith
  have he : (Real.exp (L/4))^3 = Real.exp (3*L/4) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hquad := Real.quadratic_le_exp_of_nonneg (by positivity : 0≤L/4)
  have hsmall : L^2 ≤ 32*Real.exp (L/4) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos (3*L/4)).le
  have hsum : Real.exp (L/4)*Real.exp (3*L/4)=Real.exp L := by
    rw [← Real.exp_add]; congr 1; ring
  have hbound : 3*Real.exp (3*L/4) ≤ 96*Real.exp L/L^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hL0)).mpr
    rw [mul_assoc,hsum] at hm
    nlinarith
  rw [he]
  exact (by linarith [(shiftedPrimeCutoff_bounds hL).2.2.2] :
    (shiftedPrimeCutoff L:ℝ)+2*Real.exp (3*L/4) ≤ 3*Real.exp (3*L/4)).trans hbound

end TotientAsymptotic

end

end OAI
