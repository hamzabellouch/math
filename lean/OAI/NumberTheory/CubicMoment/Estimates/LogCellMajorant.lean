import OAI.NumberTheory.CubicMoment.Estimates.LogNormCells
import OAI.NumberTheory.CubicMoment.Estimates.ThinCellCutoff

namespace OAI

/-! A concrete dispersion majorant for each actual log-norm cell. The
cell is contained in the plateau of a cutoff at a comparable scale. -/
noncomputable section
namespace CubicFirstMoment

def logCellScale (J A : ℝ) (i : ℤ) : ℝ :=
  A*Real.exp ((i:ℝ)/J)/(1+2/J)

lemma exp_inv_le_one_add {J : ℝ} (hJ : 2 ≤ J) :
    Real.exp (1/J) ≤ 1+2/J := by
  have hJp : 0 < J := by linarith
  have hr : 0 ≤ 1/J := by positivity
  have hrh : 1/J ≤ 1/2 := (div_le_div_iff₀ hJp (by norm_num)).mpr (by linarith)
  have hr1 : 1/J < 1 := by linarith
  apply (Real.exp_bound_div_one_sub_of_interval hr hr1).trans
  apply (div_le_iff₀ (sub_pos.mpr hr1)).mpr
  have hn := mul_nonneg hr (show 0 ≤ 1-2*(1/J) by linarith)
  simp only [div_eq_mul_inv,one_mul] at *
  nlinarith

lemma logCellScale_pos {J A : ℝ} (hJ : 0 < J) (hA : 0 < A) (i : ℤ) :
    0 < logCellScale J A i := by unfold logCellScale; positivity

lemma log_cell_plateau {x A J : ℝ} (hx : 0 < x) (hA : 0 < A) (hJ : 8 ≤ J)
    (i : ℤ) (hi : (i:ℝ) ≤ J*Real.log (x/A) ∧
      J*Real.log (x/A) < (i:ℝ)+1) :
    1+1/(4*(J/8)) ≤ x/logCellScale J A i ∧
      x/logCellScale J A i ≤ 1+3/(4*(J/8)) := by
  have hJp : 0 < J := by linarith
  have he : 0 < Real.exp ((i:ℝ)/J) := Real.exp_pos _
  have hr : 0 < x/A := div_pos hx hA
  have hlo : Real.exp ((i:ℝ)/J) ≤ x/A := by
    rw [←Real.exp_log hr]
    exact Real.exp_le_exp.mpr ((div_le_iff₀ hJp).mpr (by simpa only [mul_comm] using hi.1))
  have hhi : x/A ≤ Real.exp ((i:ℝ)/J)*(1+2/J) := by
    have hlog : Real.log (x/A) < ((i:ℝ)+1)/J :=
      (lt_div_iff₀ hJp).mpr (by simpa only [mul_comm] using hi.2)
    have hh := Real.exp_le_exp.mpr hlog.le
    rw [Real.exp_log hr,show ((i:ℝ)+1)/J = (i:ℝ)/J+1/J by ring,Real.exp_add] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (exp_inv_le_one_add (by linarith)) he.le)
  have hq : 0 ≤ 2/J := by positivity
  have hq1 : 2/J ≤ 1 := (div_le_one hJp).mpr (by linarith)
  have hs : x/logCellScale J A i = (x/A)*(1+2/J)/Real.exp ((i:ℝ)/J) := by
    unfold logCellScale
    field_simp
  have hl : 1+2/J ≤ x/logCellScale J A i := by
    rw [hs]
    apply (le_div_iff₀ he).mpr
    nlinarith
  have hu : x/logCellScale J A i ≤ 1+6/J := by
    rw [hs]
    apply (div_le_iff₀ he).mpr
    have hmul := mul_le_mul_of_nonneg_right hhi (show 0 ≤ 1+2/J by positivity)
    have hsquare : (1+2/J)^2 ≤ 1+6/J := by
      have hh := mul_nonneg hq (sub_nonneg.mpr hq1)
      simp only [div_eq_mul_inv] at hh ⊢
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsquare he.le]
  have he1 : 1/(4*(J/8)) = 2/J := by field_simp; norm_num
  have he3 : 3/(4*(J/8)) = 6/J := by field_simp; norm_num
  simpa only [he1,he3] using And.intro hl hu

lemma logNormCell_cutoff_one {J A : ℝ} (hJ : 8 ≤ J) (hA : 0 < A)
    {a : Eisenstein} (ha : primary a) :
    thinCellCutoff (J/8) (norm a/logCellScale J A (logNormCell J A a)) = 1 := by
  apply thinCellCutoff_one (by linarith : 0 < J/8)
  exact log_cell_plateau (norm_pos_of_ne_zero (primary_ne_zero ha)) hA hJ _
    (logNormCell_bounds J A a)

lemma logCellScale_bounds {J A Q : ℝ} (hJ : 8 ≤ J) (hA : 0 < A)
    {a : Eisenstein} (ha : primary a) (hn : 1 ≤ norm a/A ∧ norm a/A ≤ Q) :
    A/2 ≤ logCellScale J A (logNormCell J A a) ∧
      logCellScale J A (logNormCell J A a) ≤ Q*A := by
  have hJp : 0 < J := by linarith
  have hp : 0 < 1+2/J := by positivity
  have hd : 1+2/J ≤ 2 := by
    have hh : 2/J ≤ 1 := (div_le_one hJp).mpr (by linarith)
    linarith
  have hi : 0 ≤ logNormCell J A a :=
    Int.floor_nonneg.mpr (mul_nonneg hJp.le (Real.log_nonneg hn.1))
  have hei : 1 ≤ Real.exp ((logNormCell J A a:ℝ)/J) :=
    Real.one_le_exp_iff.mpr (div_nonneg (by exact_mod_cast hi) hJp.le)
  have helo : Real.exp ((logNormCell J A a:ℝ)/J) ≤ norm a/A := by
    rw [←Real.exp_log (div_pos (norm_pos_of_ne_zero (primary_ne_zero ha)) hA)]
    exact Real.exp_le_exp.mpr ((div_le_iff₀ hJp).mpr
      (by simpa only [mul_comm] using (logNormCell_bounds J A a).1))
  unfold logCellScale
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hei hA.le]
  · apply (div_le_iff₀ hp).mpr
    have hQ : 0 ≤ Q := (zero_le_one.trans hn.1).trans hn.2
    have hprod : A*Real.exp ((logNormCell J A a:ℝ)/J) ≤ Q*A := by
      have hh := mul_le_mul_of_nonneg_left (helo.trans hn.2) hA.le
      nlinarith
    have hmore := mul_nonneg (mul_nonneg hQ hA.le) (show 0 ≤ 2/J by positivity)
    nlinarith

end CubicFirstMoment

end

end OAI
