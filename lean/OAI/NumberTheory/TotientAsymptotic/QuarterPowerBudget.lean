import Mathlib

namespace OAI

/-! Elementary logarithmic budgets at a power-four-thirds threshold. -/
noncomputable section
namespace TotientAsymptotic

lemma logarithm_square_quarter_bound {b : ℝ} (hb : 1 ≤ b) :
    (Real.log (b+4))^2 ≤ 320*b^(1/4:ℝ) := by
  have hb0 : 0 < b := by linarith
  have hl : 0 ≤ Real.log (b+4) := Real.log_nonneg (by linarith)
  have hlog := Real.log_le_rpow_div (show 0 ≤ b+4 by linarith)
    (by norm_num : (0:ℝ)<1/8)
  have hq : ((b+4)^(1/8:ℝ))^2=(b+4)^(1/4:ℝ) := by
    rw [pow_two,← Real.rpow_add (by linarith : 0 < b+4)]
    norm_num
  have hp := Real.rpow_nonneg (show 0 ≤ b+4 by linarith) (1/8:ℝ)
  have hs : (Real.log (b+4))^2 ≤ 64*(b+4)^(1/4:ℝ) := by
    norm_num at hlog
    nlinarith only [hlog,hq,hl,hp]
  have ht : (b+4)^(1/4:ℝ) ≤ 5*b^(1/4:ℝ) := by
    calc
      _ ≤ (5*b)^(1/4:ℝ) := Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      _ = (5:ℝ)^(1/4:ℝ)*b^(1/4:ℝ) := Real.mul_rpow (by norm_num) hb0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num : (1:ℝ)≤5) (by norm_num))
        (Real.rpow_nonneg hb0.le _)
  linarith only [hs,ht]

lemma logarithm_budget_quarter_bound {b F : ℝ} (hb : 1 ≤ b) (hF : 0 ≤ F) :
    100*(Real.log (b+4)+F+30)^2 ≤ (10000*(F+31)^2)*b^(1/4:ℝ) := by
  have hlog := logarithm_square_quarter_bound hb
  have hs := Real.one_le_rpow hb (by norm_num : (0:ℝ)≤1/4)
  have hsum : (Real.log (b+4)+F+30)^2 ≤ 2*(Real.log (b+4))^2+2*(F+30)^2 := by
    nlinarith only [sq_nonneg (Real.log (b+4)-(F+30))]
  have hc : 64000+200*(F+30)^2 ≤ 10000*(F+31)^2 := by
    nlinarith only [hF,sq_nonneg F]
  have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg (F+30))
  have hfinal := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith : 0 ≤ b) (1/4:ℝ))
  nlinarith only [hlog,hsum,hmul,hfinal]

lemma four_thirds_threshold_budget {b F δ : ℝ} (hb : 1 ≤ b) (hF : 0 ≤ F) (hδ : 0 < δ)
    (hthreshold : ((10000*(F+31)^2)/δ)^(4/3:ℝ) ≤ b) :
    100*(Real.log (b+4)+F+30)^2 ≤ δ*b := by
  have hb0 : 0 < b := by linarith
  have hK : 0 ≤ 10000*(F+31)^2 := by positivity
  have hs : (10000*(F+31)^2)/δ ≤ b^(3/4:ℝ) := by
    have hh := Real.rpow_le_rpow
      (Real.rpow_nonneg (div_nonneg hK hδ.le) (4/3:ℝ)) hthreshold
      (by norm_num : (0:ℝ)≤3/4)
    rw [← Real.rpow_mul (div_nonneg hK hδ.le)] at hh
    norm_num at hh
    exact hh
  have hc : 10000*(F+31)^2 ≤ δ*b^(3/4:ℝ) := by
    have hh := (div_le_iff₀ hδ).mp hs
    linarith only [hh]
  have hm := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hb0.le (1/4:ℝ))
  have he : δ*b^(3/4:ℝ)*b^(1/4:ℝ)=δ*b := by
    rw [mul_assoc,← Real.rpow_add hb0]
    norm_num
  exact (logarithm_budget_quarter_bound hb hF).trans (by simpa only [he] using hm)

lemma four_thirds_threshold_tail {b F δ : ℝ} (hb : 1 ≤ b) (hF : 0 ≤ F)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hthreshold : ((10000*(F+31)^2)/δ)^(4/3:ℝ) ≤ b) :
    δ⁻¹ ≤ Real.exp (δ*b) := by
  have hK : 1 ≤ 10000*(F+31)^2 := by nlinarith only [hF,sq_nonneg F]
  have hratio : δ⁻¹ ≤ (10000*(F+31)^2)/δ := by
    simpa only [one_div] using div_le_div_of_nonneg_right hK hδ.le
  have hi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hr : 1 ≤ (10000*(F+31)^2)/δ := hi.trans hratio
  have hp : (10000*(F+31)^2)/δ ≤ ((10000*(F+31)^2)/δ)^(4/3:ℝ) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hr (by norm_num : (1:ℝ)≤4/3))
  have hib : δ⁻¹ ≤ b := hratio.trans (hp.trans hthreshold)
  have hlog : Real.log (δ⁻¹) ≤ Real.log (b+4) :=
    Real.log_le_log (inv_pos.mpr hδ) (by linarith only [hib])
  have hl : 0 ≤ Real.log (b+4) := Real.log_nonneg (by linarith)
  have hbudget := four_thirds_threshold_budget hb hF hδ hthreshold
  have hs : Real.log (b+4) ≤ 100*(Real.log (b+4)+F+30)^2 := by
    nlinarith only [hl,hF,sq_nonneg (Real.log (b+4)),sq_nonneg F]
  exact (Real.log_le_iff_le_exp (inv_pos.mpr hδ)).mp (hlog.trans (hs.trans hbudget))

def rowMassCutoffHeight (F δ : ℝ) : ℝ :=
  1000000000*((10000*(F+31)^2)/δ)^(4/3:ℝ)

lemma row_mass_cutoff_height_bounds {F δ ω : ℝ} (hF : 0 ≤ F)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hδω : 64000000*δ ≤ ω^2) :
    10000 ≤ rowMassCutoffHeight F δ ∧
    (8000/ω)^2 ≤ rowMassCutoffHeight F δ ∧
    max 300000000 (((10000*(F+31)^2)/δ)^(4/3:ℝ)) ≤ rowMassCutoffHeight F δ-1 ∧
    4 ≤ (ω/2)*rowMassCutoffHeight F δ ∧
    δ⁻¹ ≤ Real.exp (δ*rowMassCutoffHeight F δ) := by
  let R := ((10000*(F+31)^2)/δ)^(4/3:ℝ)
  have hK : 1 ≤ 10000*(F+31)^2 := by nlinarith only [hF,sq_nonneg F]
  have hi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hir : δ⁻¹ ≤ (10000*(F+31)^2)/δ := by
    simpa only [one_div] using div_le_div_of_nonneg_right hK hδ.le
  have hr : 1 ≤ (10000*(F+31)^2)/δ := hi.trans hir
  have hR : (10000*(F+31)^2)/δ ≤ R := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hr (by norm_num : (1:ℝ)≤4/3)
  have hR1 : 1 ≤ R := hr.trans hR
  have hdR : 1 ≤ δ*R := by
    have hh := mul_le_mul_of_nonneg_left (hir.trans hR) hδ.le
    simpa only [mul_inv_cancel₀ hδ.ne'] using hh
  have hb : rowMassCutoffHeight F δ=1000000000*R := rfl
  have hdb : 1000000000 ≤ δ*rowMassCutoffHeight F δ := by
    rw [hb]
    nlinarith only [hdR]
  have hb0 : 0 ≤ rowMassCutoffHeight F δ := by rw [hb]; positivity
  have hwb : 64000000 ≤ ω^2*rowMassCutoffHeight F δ := by
    have hh := mul_le_mul_of_nonneg_right hδω hb0
    nlinarith only [hh,hdb]
  have hhead : (8000/ω)^2 ≤ rowMassCutoffHeight F δ := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hω)).mpr
    nlinarith only [hwb]
  have hωsq : ω^2 ≤ ω := by nlinarith only [hω,hω1]
  have hlinear := mul_le_mul_of_nonneg_right hωsq hb0
  have hthreshold : R ≤ rowMassCutoffHeight F δ-1 := by rw [hb]; linarith only [hR1]
  refine ⟨by rw [hb]; linarith only [hR1],hhead,
    max_le (by rw [hb]; linarith only [hR1]) hthreshold,
    by nlinarith only [hlinear,hwb],?_⟩
  exact four_thirds_threshold_tail (by rw [hb]; linarith only [hR1]) hF hδ hδ1
    (hthreshold.trans (by linarith))

lemma row_mass_cutoff_log_bound {F δ : ℝ} (hF : 0 ≤ F)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log (rowMassCutoffHeight F δ+4) ≤ Real.log 2000000000+
      (4/3:ℝ)*(Real.log (10000*(F+31)^2)-Real.log δ) := by
  have hK : 1 ≤ 10000*(F+31)^2 := by nlinarith only [hF,sq_nonneg F]
  have hr : 1 ≤ (10000*(F+31)^2)/δ :=
    (le_div_iff₀ hδ).mpr (by linarith only [hK,hδ1])
  have hR : 1 ≤ ((10000*(F+31)^2)/δ)^(4/3:ℝ) :=
    Real.one_le_rpow hr (by norm_num)
  have hp : 0 < ((10000*(F+31)^2)/δ)^(4/3:ℝ) := by positivity
  have hle : rowMassCutoffHeight F δ+4 ≤
      2000000000*((10000*(F+31)^2)/δ)^(4/3:ℝ) := by
    unfold rowMassCutoffHeight
    linarith only [hR]
  calc
    _ ≤ Real.log (2000000000*((10000*(F+31)^2)/δ)^(4/3:ℝ)) :=
      Real.log_le_log (by unfold rowMassCutoffHeight; positivity) hle
    _ = _ := by
      rw [Real.log_mul (by norm_num : (2000000000:ℝ)≠0) hp.ne',Real.log_rpow
        (div_pos (by linarith only [hK]) hδ),Real.log_div (by linarith only [hK]) hδ.ne']

end TotientAsymptotic

end

end OAI
