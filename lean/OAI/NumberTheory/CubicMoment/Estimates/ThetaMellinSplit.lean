import OAI.NumberTheory.CubicMoment.Estimates.ThetaUpperMellin

namespace OAI

/-! The completed theta Mellin transform as two rapidly convergent tails. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace CubicFirstMoment

def thetaUpper (f : ℝ → ℂ) : ℝ → ℂ := (Ioi 1).indicator f

lemma mellin_thetaUpper (f : ℝ → ℂ) (s : ℂ) :
    mellin (thetaUpper f) s = ∫ t : ℝ in Ioi 1, (t:ℂ)^(s-1)*f t := by
  simp only [mellin,thetaUpper,← indicator_smul]
  rw [setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))]
  rfl

lemma thetaUpper_mellinConvergent {f : ℝ → ℂ} {C c : ℝ}
    (hc : 0 < c) (hfcont : ContinuousOn f (Ioi 0))
    (hf : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C*Real.exp (-c*t)) (s : ℂ) :
    MellinConvergent (thetaUpper f) s := by
  simp only [MellinConvergent,thetaUpper,← indicator_smul]
  rw [IntegrableOn,integrable_indicator_iff measurableSet_Ioi]
  change Integrable _ ((volume.restrict (Ioi 0)).restrict (Ioi 1))
  rw [Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))]
  exact theta_upper_integrable hc hfcont hf s

lemma theta_mellin_split {f g : ℝ → ℂ} {ε : ℂ}
    (hFE : ∀ t : ℝ, 0 < t → f (1/t) = ε*(t:ℂ)*g t)
    {s : ℂ} (hf : MellinConvergent (thetaUpper f) s)
    (hg : MellinConvergent (thetaUpper g) (1-s)) :
    mellin f s = mellin (thetaUpper f) s + ε*mellin (thetaUpper g) (1-s) := by
  let v : ℝ → ℂ := fun t => ε • ((t:ℂ)^(-1:ℂ) • thetaUpper g t⁻¹)
  have hginv : MellinConvergent (fun t : ℝ => thetaUpper g t⁻¹) (s-1) := by
    have he : (s-1)/(-1:ℝ) = 1-s := by push_cast; ring
    rw [← he] at hg
    simpa only [Real.rpow_neg_one] using
      (MellinConvergent.comp_rpow (by norm_num : (-1:ℝ) ≠ 0)).mpr hg
  have hv : MellinConvergent v s := by
    exact (MellinConvergent.cpow_smul.mpr (by simpa only [sub_eq_add_neg] using hginv)).const_smul ε
  have hid : f =ᵐ[volume.restrict (Ioi 0)] (fun t => thetaUpper f t + v t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      (volume.restrict (Ioi 0)).ae_ne 1] with t ht ht1
    change 0 < t at ht
    rcases lt_or_gt_of_ne ht1 with hlt | hgt
    · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr hlt
      have ht' := hFE t⁻¹ (inv_pos.mpr ht)
      simp only [one_div,inv_inv,Complex.ofReal_inv] at ht'
      rw [thetaUpper,indicator_of_notMem (show t ∉ Ioi (1:ℝ) from not_lt.mpr hlt.le),zero_add]
      dsimp only [v]
      rw [thetaUpper,indicator_of_mem (show t⁻¹ ∈ Ioi (1:ℝ) from hinv),smul_eq_mul,smul_eq_mul,
        Complex.cpow_neg_one]
      simpa only [mul_assoc] using ht'
    · have hinv : t⁻¹ < 1 := (inv_lt_one₀ ht).mpr hgt
      rw [thetaUpper,indicator_of_mem (show t ∈ Ioi (1:ℝ) from hgt)]
      dsimp only [v]
      rw [thetaUpper,indicator_of_notMem (show t⁻¹ ∉ Ioi (1:ℝ) from not_lt.mpr hinv.le)]
      simp
  calc
    mellin f s = mellin (fun t => thetaUpper f t + v t) s := by
      apply integral_congr_ae
      filter_upwards [hid] with t ht
      rw [ht]
    _ = mellin (thetaUpper f) s + mellin v s := (hasMellin_add hf hv).2
    _ = _ := by
      dsimp only [v]
      rw [mellin_const_smul,mellin_cpow_smul,mellin_comp_inv]
      simp only [smul_eq_mul,show -(s+(-1:ℂ)) = 1-s by ring]

end CubicFirstMoment

end

end OAI
