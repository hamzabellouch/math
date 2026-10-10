import OAI.NumberTheory.CubicMoment.Estimates.HeightBilinearScale

namespace OAI

/-! Unsquaring a two-sided height mean, including zero coefficient energy. -/
noncomputable section
namespace CubicFirstMoment

lemma dyadicHeightMean_norm_le_of_sq_le_nonneg {f : ℝ → ℂ} (hf : Continuous f)
    {T R : ℝ} (hT : 0 < T) (hR : 0 ≤ R)
    (hsq : dyadicHeightMean (fun t => ‖f t‖^2) T ≤ R^2) :
    dyadicHeightMean (fun t => ‖f t‖) T ≤ 2*R := by
  by_cases hp : 0 < R
  · exact dyadicHeightMean_norm_le_of_sq_le hf hT hp hsq
  have hz : R = 0 := le_antisymm (le_of_not_gt hp) hR
  subst R
  by_contra hh
  have hm : 0 < dyadicHeightMean (fun t => ‖f t‖) T := by linarith
  have hb := dyadicHeightMean_norm_le_of_sq_le hf hT
    (R := dyadicHeightMean (fun t => ‖f t‖) T/4) (by positivity)
    (hsq.trans (by nlinarith [sq_nonneg (dyadicHeightMean (fun t => ‖f t‖) T/4)]))
  linarith

lemma dyadicHeightMean_norm_le_sqrt {f : ℝ → ℂ} (hf : Continuous f)
    {T R : ℝ} (hT : 0 < T) (hR : 0 ≤ R)
    (hsq : dyadicHeightMean (fun t => ‖f t‖^2) T ≤ R) :
    dyadicHeightMean (fun t => ‖f t‖) T ≤ 2*Real.sqrt R := by
  exact dyadicHeightMean_norm_le_of_sq_le_nonneg hf hT (Real.sqrt_nonneg _)
    (by rwa [Real.sq_sqrt hR])

lemma height_cell_square_root {f : ℝ → ℂ} (hf : Continuous f)
    {T K D E a b : ℝ} (hT : 0 < T) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsq : dyadicHeightMean (fun t => ‖f t‖^2) T ≤ K*(D+E)*a*b) :
    dyadicHeightMean (fun t => ‖f t‖) T ≤
      2*Real.sqrt K*(Real.sqrt D+Real.sqrt E)*Real.sqrt a*Real.sqrt b := by
  have hh := dyadicHeightMean_norm_le_sqrt hf hT (by positivity : 0 ≤ K*(D+E)*a*b) hsq
  rw [Real.sqrt_mul (by positivity : 0 ≤ K*(D+E)*a),
    Real.sqrt_mul (by positivity : 0 ≤ K*(D+E)),Real.sqrt_mul hK] at hh
  have he : Real.sqrt (D+E) ≤ Real.sqrt D+Real.sqrt E := by
    nlinarith [Real.sq_sqrt (add_nonneg hD hE),Real.sq_sqrt hD,Real.sq_sqrt hE,
      Real.sqrt_nonneg (D+E),Real.sqrt_nonneg D,Real.sqrt_nonneg E,
      mul_nonneg (Real.sqrt_nonneg D) (Real.sqrt_nonneg E)]
  apply hh.trans
  nlinarith [mul_nonneg (show 0 ≤ 2*Real.sqrt K*Real.sqrt a*Real.sqrt b by positivity)
    (sub_nonneg.mpr he)]

end CubicFirstMoment

end

end OAI
