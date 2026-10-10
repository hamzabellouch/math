import OAI.Analysis.IntegralMeans.SharpModel

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Brennan.Sharp

lemma koebeInverse_left_inverse {z : ℂ} (hz : z ∈ disk) :
    koebeInverse (koebeMap z) = z :=
  koebeMap_schlicht.1.2.leftInvOn_invFunOn hz

lemma koebeInverse_mapsTo : MapsTo koebeInverse koebeDomain disk := by
  rintro _ ⟨z, hz, rfl⟩
  rwa [koebeInverse_left_inverse hz]

lemma koebeInverse_right_inverse {z : ℂ} (hz : z ∈ koebeDomain) :
    koebeMap (koebeInverse z) = z := by
  rcases hz with ⟨w, hw, rfl⟩
  rw [koebeInverse_left_inverse hw]

lemma koebe_deriv_norm_left {w : ℂ} (hz : -1 + w ∈ disk) :
    ‖deriv koebeMap (-1 + w)‖ = ‖w‖ / ‖2 - w‖ ^ 3 := by
  rw [(koebeMap_hasDerivAt hz).deriv]
  have hnum : 1 + (-1 + w) = w := by ring
  have hden : 1 - (-1 + w) = 2 - w := by ring
  rw [hnum, hden, norm_div, norm_pow]

lemma koebe_deriv_norm_right {w : ℂ} (hz : 1 - w ∈ disk) :
    ‖deriv koebeMap (1 - w)‖ = ‖2 - w‖ / ‖w‖ ^ 3 := by
  rw [(koebeMap_hasDerivAt hz).deriv]
  have hnum : 1 + (1 - w) = 2 - w := by ring
  have hden : 1 - (1 - w) = w := by ring
  rw [hnum, hden, norm_div, norm_pow]

lemma one_le_norm_two_sub {w : ℂ} (hw : ‖w‖ < 1 / 2) :
    1 ≤ ‖2 - w‖ := by
  have h := norm_sub_norm_le (2 : ℂ) w
  norm_num at h
  linarith

lemma koebe_negative_endpoint_lower {w : ℂ}
    (hz : -1 + w ∈ disk) (hw : ‖w‖ < 1 / 2) :
    ‖w‖ ^ (-2 : ℝ) ≤ ‖deriv koebeMap (-1 + w)‖ ^ (-2 : ℝ) := by
  have hd : 0 < ‖deriv koebeMap (-1 + w)‖ :=
    norm_pos_iff.mpr (univalent_deriv_ne_zero Metric.isOpen_ball koebeMap_schlicht.1 hz)
  have hb : ‖deriv koebeMap (-1 + w)‖ ≤ ‖w‖ := by
    rw [koebe_deriv_norm_left hz]
    exact div_le_self (norm_nonneg _) (one_le_pow₀ (one_le_norm_two_sub hw))
  exact Real.rpow_le_rpow_of_nonpos hd hb (by norm_num)

lemma koebe_positive_endpoint_lower {w : ℂ}
    (hz : 1 - w ∈ disk) (h0 : 0 < ‖w‖) (hw : ‖w‖ < 1 / 2) :
    ‖w‖ ^ (-2 : ℝ) ≤ ‖deriv koebeMap (1 - w)‖ ^ (2 / 3 : ℝ) := by
  have hb : 1 / ‖w‖ ^ 3 ≤ ‖deriv koebeMap (1 - w)‖ := by
    rw [koebe_deriv_norm_right hz]
    exact div_le_div_of_nonneg_right (one_le_norm_two_sub hw) (by positivity)
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1 / ‖w‖ ^ 3) hb
    (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have he : (1 / ‖w‖ ^ 3) ^ (2 / 3 : ℝ) = ‖w‖ ^ (-2 : ℝ) := by
    rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_natCast ‖w‖ 3,
      ← Real.rpow_mul h0.le]
    norm_num [Real.rpow_neg, Real.rpow_two]
  rwa [he] at hp

end Brennan.Sharp

end

end OAI
