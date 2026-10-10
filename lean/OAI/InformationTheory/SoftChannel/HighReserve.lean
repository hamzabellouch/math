import OAI.InformationTheory.SoftChannel.Payment

namespace OAI

section

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace LeanBlast.CourtadeKumar

def softCutoff : ℝ := psi (77/100)
def centeredRate (I : ℝ) : ℝ := (I-(ell-1/2))*(rDeriv I-2)-rGap I

def meanReserve (m I : ℝ) : ℝ :=
  2*I+(1-m^2)*L ((entropy m-I)/(1-m^2))

lemma softCutoff_pos : 0 < softCutoff := psi_pos_of_pos (by norm_num) (by norm_num)
lemma softCutoff_lt_ell : softCutoff < ell := psi_lt_ell (by norm_num)

lemma artanh_77_upper : Real.artanh (77/100:ℝ) < 1021/1000 := by
  have he : (177/23:ℝ) < Real.exp (1021/500) := by
    refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 1021/500) 8)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hl := (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ)<177/23)).mpr he
  rw [artanh_eq_log_sub (by norm_num : (77/100:ℝ) ∈ Ioo (-1) 1)]
  rw [← Real.log_div (by norm_num : (1+(77/100:ℝ)) ≠ 0) (by norm_num : (1-(77/100:ℝ)) ≠ 0)]
  norm_num at *
  linarith

lemma softCutoff_lower : (336/1000:ℝ) ≤ softCutoff := by
  have h := sum_range_psi_le (by norm_num : |(77/100:ℝ)| < 1) 6
  norm_num [psiCoeff, Finset.sum_range_succ] at h
  exact le_trans (by norm_num) h

lemma softCutoff_above_center : ell-1/2 < softCutoff := by
  linarith [ell_lt_347_div_500,softCutoff_lower]

lemma centeredRate_cutoff_pos : 0 < centeredRate softCutoff := by
  have hv0 := Real.artanh_pos (show (77/100:ℝ) ∈ Ioo 0 1 by norm_num)
  have hv := artanh_77_upper
  have hs := softCutoff_lower
  have hL := ell_lt_347_div_500
  have hD : (185/100:ℝ) ≤ (77/100)/((1-(77/100:ℝ)^2)*Real.artanh (77/100)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  unfold centeredRate rGap
  rw [show softCutoff = psi (77/100) from rfl, rDeriv_psi (by norm_num), r_psi (by norm_num)]
  change 0 < (softCutoff-(ell-1/2))*(1+(77/100)/((1-(77/100:ℝ)^2)*Real.artanh (77/100))-2)-
    ((77/100)*Real.artanh (77/100)-2*softCutoff)
  have hmul := mul_le_mul_of_nonneg_left (show (85/100:ℝ) ≤ 1+(77/100)/((1-(77/100:ℝ)^2)*Real.artanh (77/100))-2 by linarith)
    (sub_nonneg.mpr softCutoff_above_center.le)
  nlinarith

lemma hasDerivAt_centeredRate {I : ℝ} (hI : I ∈ Ioo 0 ell) :
    HasDerivAt centeredRate ((I-(ell-1/2))*rSecondDeriv I) I := by
  have h := (((hasDerivAt_id I).sub_const (ell-1/2)).mul
    ((hasDerivAt_rDeriv hI).sub_const 2)).sub (hasDerivAt_rGap hI)
  convert! h using 1; dsimp [centeredRate]; ring

lemma centeredRate_nonneg {I : ℝ} (hI : I ∈ Ico softCutoff ell) : 0 ≤ centeredRate I := by
  have hm : MonotoneOn centeredRate (Ico softCutoff ell) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun I => (I-(ell-1/2))*rSecondDeriv I)
      (convex_Ico _ _)
    · intro x hx
      exact (hasDerivAt_centeredRate ⟨softCutoff_pos.trans_le hx.1,hx.2⟩).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_centeredRate ⟨by simp only [interior_Ico,mem_Ioo] at hx; exact softCutoff_pos.trans hx.1,
        by simp only [interior_Ico,mem_Ioo] at hx; exact hx.2⟩).hasDerivWithinAt
    · intro x hx
      simp only [interior_Ico,mem_Ioo] at hx
      exact mul_nonneg (by linarith [softCutoff_above_center])
        (rSecondDeriv_nonneg (by linarith [softCutoff_pos]) hx.2)
  exact centeredRate_cutoff_pos.le.trans (hm ⟨le_rfl,softCutoff_lt_ell⟩ hI hI.1)

lemma rGap_tangent {I s : ℝ} (hI : I ∈ Ioo 0 ell) (hs : s ∈ Ico I ell) :
    rGap I+(s-I)*(rDeriv I-2) ≤ rGap s := by
  rcases hs.1.eq_or_lt with he | hlt
  · rw [← he]; simp
  · have h := convexOn_rGap.le_slope_of_hasDerivAt ⟨hI.1.le,hI.2⟩ ⟨hI.1.le.trans hs.1,hs.2⟩ hlt
      (hasDerivAt_rGap hI)
    rw [slope_def_field] at h
    have hh := (le_div_iff₀ (sub_pos.mpr hlt)).mp h
    nlinarith

lemma high_information_reserve {m I : ℝ} (hm : |m| < 1)
    (hI : softCutoff ≤ I) (hIe : I < entropy m) : r I ≤ meanReserve m I := by
  have hm2 : m^2 < 1 := by nlinarith [abs_lt.mp hm, sq_abs m]
  have ha : 0 < 1-m^2 := by linarith
  have hI0 : 0 < I := softCutoff_pos.trans_le hI
  have hIL : I < ell := hIe.trans_le (entropy_le_ell m)
  have hc := half_sq_le_psi hm.le
  let c := entropy m-(1-m^2)*ell
  have hcub : c ≤ m^2*(ell-1/2) := by dsimp [c,entropy]; nlinarith
  let s := ell-(entropy m-I)/(1-m^2)
  have hsline : (1-m^2)*s = I-c := by dsimp [s,c]; field_simp; ring
  have hsI : I ≤ s := by
    have hp := mul_nonneg (sq_nonneg m) (show 0 ≤ I-(ell-1/2) by linarith [softCutoff_above_center])
    nlinarith
  have hsL : s < ell := by dsimp [s]; exact sub_lt_self _ (div_pos (sub_pos.mpr hIe) ha)
  have hL : L ((entropy m-I)/(1-m^2)) = rGap s := by
    rw [L_eq_rGap ⟨div_pos (sub_pos.mpr hIe) ha,by dsimp [s] at hsI; linarith⟩]
  have htan := mul_le_mul_of_nonneg_left (rGap_tangent ⟨hI0,hIL⟩ ⟨hsI,hsL⟩) ha.le
  have hcd := mul_le_mul_of_nonneg_right hcub (sub_nonneg.mpr (rDeriv_ge_two hI0.le hIL))
  have hxi := mul_nonneg (sq_nonneg m) (centeredRate_nonneg ⟨hI,hIL⟩)
  have hident := congrArg (fun t => t*(rDeriv I-2)) hsline
  unfold centeredRate at hxi
  unfold meanReserve
  rw [hL]
  dsimp [rGap] at *
  nlinarith

lemma meanReserve_zero_mean {I : ℝ} (hI : I ∈ Ico 0 ell) : meanReserve 0 I = r I := by
  simp only [meanReserve, entropy_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sub_zero, div_one, one_mul]
  rw [L_ell_sub hI.1 hI.2]
  ring

end LeanBlast.CourtadeKumar
end
end

end OAI
