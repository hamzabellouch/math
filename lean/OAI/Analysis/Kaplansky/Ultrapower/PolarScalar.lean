import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.StableFiniteness.Definitions

namespace OAI

noncomputable section

namespace KaplanskyConsequences.PolarScalar


def invCut (r t : ℝ) : ℝ := (Real.sqrt (max t r))⁻¹
def cut (r t : ℝ) : ℝ := t / max t r

lemma max_pos {r : ℝ} (hr : 0 < r) (t : ℝ) : 0 < max t r := hr.trans_le (le_max_right ..)
lemma continuous_invCut {r : ℝ} (hr : 0 < r) : Continuous (invCut r) :=
  ((continuous_id.max continuous_const).sqrt).inv₀ fun t => (Real.sqrt_pos.2 (max_pos hr t)).ne'
lemma continuous_cut {r : ℝ} (hr : 0 < r) : Continuous (cut r) :=
  continuous_id.div (continuous_id.max continuous_const) (fun t => (max_pos hr t).ne')

lemma invCut_nonneg {r : ℝ} (hr : 0 < r) (t : ℝ) : 0 ≤ invCut r t := by unfold invCut; positivity
lemma cut_nonneg {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) : 0 ≤ cut r t := div_nonneg ht (max_pos hr t).le
lemma cut_le_one {r t : ℝ} (hr : 0 < r) : cut r t ≤ 1 :=
  (div_le_one (max_pos hr t)).mpr (le_max_left ..)

lemma cut_eq {r : ℝ} (hr : 0 < r) (t : ℝ) : invCut r t*t*invCut r t=cut r t := by
  have hs : (Real.sqrt (max t r))^2=max t r := Real.sq_sqrt (max_pos hr t).le
  unfold invCut cut
  calc
    (Real.sqrt (max t r))⁻¹ * t * (Real.sqrt (max t r))⁻¹ =
        t * ((Real.sqrt (max t r))^2)⁻¹ := by ring
    _ = t * (max t r)⁻¹ := by rw [hs]
    _ = t / max t r := by rw [div_eq_mul_inv]

lemma cut_mono {r s t : ℝ} (hr : 0 < r) (hs : 0 < s) (ht : 0 ≤ t) (hrs : r ≤ s) :
    cut s t ≤ cut r t :=
  (div_le_div_iff₀ (max_pos hs t) (max_pos hr t)).2
    (mul_le_mul_of_nonneg_left (max_le_max_left t hrs) ht)

lemma cut_gap {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    cut r t*(cut r t-1)^2 ≤ cut (r/2) t-cut r t := by
  have hg0 := cut_nonneg hr ht
  have hg1 := cut_le_one (t:=t) hr
  have h01 : (cut r t-1)^2 ≤ 1 := by nlinarith
  by_cases htr : t ≤ r/2
  · have htr' : t ≤ r := htr.trans (by linarith)
    have hm : cut (r/2) t = 2*cut r t := by
      simp only [cut,max_eq_right htr,max_eq_right htr']
      field_simp
    rw [hm]
    nlinarith [mul_le_mul_of_nonneg_left h01 hg0]
  · have htpos : 0 < t := lt_of_lt_of_le (half_pos hr) (not_le.mp htr).le
    have hm : cut (r/2) t=1 := by
      rw [cut,max_eq_left (not_le.mp htr).le,div_self htpos.ne']
    rw [hm]
    have hsq : (cut r t-1)^2 ≤ 1-cut r t := by nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hg1)]
    have hm' := mul_le_mul_of_nonneg_right hg1 (sq_nonneg (cut r t-1))
    nlinarith

lemma cut_error {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    0 ≤ t*(invCut r t*Real.sqrt t-1)^2 ∧ t*(invCut r t*Real.sqrt t-1)^2 ≤ r := by
  refine ⟨mul_nonneg ht (sq_nonneg _),?_⟩
  by_cases htr : r ≤ t
  · have htpos : 0 < t := hr.trans_le htr
    have he : invCut r t*Real.sqrt t=1 := by
      unfold invCut
      rw [max_eq_left htr,inv_mul_cancel₀ (Real.sqrt_pos.2 htpos).ne']
    rw [he,sub_self,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero]
    exact hr.le
  · have htr' : t ≤ r := (not_le.mp htr).le
    have hs0 : 0 ≤ invCut r t*Real.sqrt t := mul_nonneg (invCut_nonneg hr t) (Real.sqrt_nonneg t)
    have hs1 : invCut r t*Real.sqrt t ≤ 1 := by
      rw [invCut,max_eq_right htr',mul_comm,← div_eq_mul_inv]
      exact (div_le_one (Real.sqrt_pos.2 hr)).mpr (Real.sqrt_le_sqrt htr')
    have hsq : (invCut r t*Real.sqrt t-1)^2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq ht]


end KaplanskyConsequences.PolarScalar

end

end OAI
