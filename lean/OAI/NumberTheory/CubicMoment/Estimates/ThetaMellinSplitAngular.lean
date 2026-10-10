import OAI.NumberTheory.CubicMoment.Estimates.ThetaMellinSplit

namespace OAI

/-! The even-weight Mellin split for the actual angular derivatives. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace CubicFirstMoment

lemma theta_mellin_split_angular (k : ℕ) {f g : ℝ → ℂ} {ε : ℂ}
    (hFE : ∀ t : ℝ,0<t → f (1/t)=ε*(t:ℂ)^(2*k)*g t)
    {s : ℂ} (hf : MellinConvergent (thetaUpper f) s)
    (hg : MellinConvergent (thetaUpper g) (((2*k:ℕ):ℂ)-s)) :
    MellinConvergent f s ∧
      mellin f s=mellin (thetaUpper f) s+ε*mellin (thetaUpper g) (((2*k:ℕ):ℂ)-s) := by
  let v : ℝ → ℂ := fun t => ε • ((t:ℂ)^(-((2*k:ℕ):ℂ)) • thetaUpper g t⁻¹)
  have hginv : MellinConvergent (fun t : ℝ => thetaUpper g t⁻¹) (s-((2*k:ℕ):ℂ)) := by
    have he : (s-((2*k:ℕ):ℂ))/(-1:ℝ)=((2*k:ℕ):ℂ)-s := by push_cast; ring
    rw [←he] at hg
    simpa only [Real.rpow_neg_one] using
      (MellinConvergent.comp_rpow (by norm_num : (-1:ℝ)≠0)).mpr hg
  have hv : MellinConvergent v s :=
    (MellinConvergent.cpow_smul.mpr (by simpa only [sub_eq_add_neg] using hginv)).const_smul ε
  have hid : f=ᵐ[volume.restrict (Ioi 0)] (fun t => thetaUpper f t+v t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      (volume.restrict (Ioi 0)).ae_ne 1] with t ht ht1
    change 0<t at ht
    rcases lt_or_gt_of_ne ht1 with hlt | hgt
    · have hinv : 1<t⁻¹ := (one_lt_inv₀ ht).mpr hlt
      have ht' := hFE t⁻¹ (inv_pos.mpr ht)
      simp only [one_div,inv_inv,Complex.ofReal_inv] at ht'
      rw [thetaUpper,indicator_of_notMem (show t∉Ioi (1:ℝ) from not_lt.mpr hlt.le),zero_add]
      dsimp only [v]
      rw [thetaUpper,indicator_of_mem (show t⁻¹∈Ioi (1:ℝ) from hinv),smul_eq_mul,smul_eq_mul]
      rw [Complex.cpow_neg,Complex.cpow_natCast]
      simpa only [inv_pow,mul_assoc] using ht'
    · have hinv : t⁻¹<1 := (inv_lt_one₀ ht).mpr hgt
      rw [thetaUpper,indicator_of_mem (show t∈Ioi (1:ℝ) from hgt)]
      dsimp only [v]
      rw [thetaUpper,indicator_of_notMem (show t⁻¹∉Ioi (1:ℝ) from not_lt.mpr hinv.le)]
      simp
  have hsum := hasMellin_add hf hv
  constructor
  · apply hsum.1.congr
    filter_upwards [hid] with t ht
    rw [ht]
  · calc
      mellin f s=mellin (fun t => thetaUpper f t+v t) s := by
        apply integral_congr_ae
        filter_upwards [hid] with t ht
        rw [ht]
      _ = mellin (thetaUpper f) s+mellin v s := hsum.2
      _ = _ := by
        dsimp only [v]
        rw [mellin_const_smul,mellin_cpow_smul,mellin_comp_inv]
        simp only [smul_eq_mul,show -(s+(-((2*k:ℕ):ℂ)))=((2*k:ℕ):ℂ)-s by ring]

end CubicFirstMoment

end

end OAI
