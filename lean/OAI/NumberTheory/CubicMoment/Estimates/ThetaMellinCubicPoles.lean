import OAI.NumberTheory.CubicMoment.Estimates.ThetaMellinSplit

namespace OAI

/-! The cubic theta Mellin split with its two possible constant terms. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma theta_mellin_split_cubic_poles {f g : ℝ → ℂ} {a b : ℂ}
    (hFE : ∀ t : ℝ, 0<t → f t=g t⁻¹+a*(t:ℂ)^(-(2/3:ℂ))+b*(t:ℂ)^(2/3:ℂ))
    {s : ℂ} (hs : 2/3<s.re)
    (hf : MellinConvergent (thetaUpper f) s)
    (hg : MellinConvergent (thetaUpper g) (-s)) :
    MellinConvergent f s ∧ mellin f s=
      mellin (thetaUpper f) s+mellin (thetaUpper g) (-s)+a/(s-2/3)+b/(s+2/3) := by
  have hI : MellinConvergent (fun t => thetaUpper g t⁻¹) s := by
    have he : s/(-1:ℝ)= -s := by push_cast; ring
    rw [←he] at hg
    simpa only [Real.rpow_neg_one] using
      (MellinConvergent.comp_rpow (by norm_num : (-1:ℝ)≠0)).mpr hg
  have hm := hasMellin_cpow_Ioc (-(2/3:ℂ)) (s:=s) (by norm_num; linarith)
  have hp := hasMellin_cpow_Ioc (2/3:ℂ) (s:=s) (by norm_num; linarith)
  have hA := hasMellin_const_smul hm.1 a
  have hB := hasMellin_const_smul hp.1 b
  have hS := hasMellin_add (hasMellin_add (hasMellin_add hf hI).1 hA.1).1 hB.1
  simp only [smul_eq_mul] at hA hB hS
  have hid : f =ᵐ[volume.restrict (Ioi 0)] fun t =>
      thetaUpper f t+thetaUpper g t⁻¹+
        a*(Ioc (0:ℝ) 1).indicator (fun t : ℝ => (t:ℂ)^(-(2/3:ℂ))) t+
        b*(Ioc (0:ℝ) 1).indicator (fun t : ℝ => (t:ℂ)^(2/3:ℂ)) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      (volume.restrict (Ioi 0)).ae_ne 1] with t ht ht1
    change 0<t at ht
    rcases lt_or_gt_of_ne ht1 with hlt | hgt
    · have hinv : 1<t⁻¹ := (one_lt_inv₀ ht).mpr hlt
      simp only [thetaUpper,indicator_of_notMem (show t∉Ioi (1:ℝ) from not_lt.mpr hlt.le),
        indicator_of_mem (show t⁻¹∈Ioi (1:ℝ) from hinv),zero_add,
        indicator_of_mem (show t∈Ioc (0:ℝ) 1 from ⟨ht,hlt.le⟩)]
      exact hFE t ht
    · have hinv : t⁻¹<1 := (inv_lt_one₀ ht).mpr hgt
      simp only [thetaUpper,indicator_of_mem (show t∈Ioi (1:ℝ) from hgt),
        indicator_of_notMem (show t⁻¹∉Ioi (1:ℝ) from not_lt.mpr hinv.le),
        indicator_of_notMem (show t∉Ioc (0:ℝ) 1 from fun h => not_le_of_gt hgt h.2),
        mul_zero,add_zero]
  constructor
  · apply hS.1.congr
    filter_upwards [hid] with t ht
    rw [ht]
  · calc
      mellin f s = mellin (fun t => thetaUpper f t+thetaUpper g t⁻¹+
        a*(Ioc (0:ℝ) 1).indicator (fun t : ℝ => (t:ℂ)^(-(2/3:ℂ))) t+
        b*(Ioc (0:ℝ) 1).indicator (fun t : ℝ => (t:ℂ)^(2/3:ℂ)) t) s := by
          apply integral_congr_ae
          filter_upwards [hid] with t ht
          rw [ht]
      _ = _ := by
        rw [hS.2,(hasMellin_add (hasMellin_add hf hI).1 hA.1).2,
          (hasMellin_add hf hI).2,hA.2,hB.2,hm.2,hp.2,mellin_comp_inv]
        simp only [div_eq_mul_inv,sub_eq_add_neg,one_mul]

end CubicFirstMoment

end

end OAI
