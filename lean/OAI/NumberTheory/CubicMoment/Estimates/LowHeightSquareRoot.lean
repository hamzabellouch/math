import OAI.NumberTheory.CubicMoment.Estimates.HeightSquareRoot

namespace OAI
noncomputable section
namespace CubicFirstMoment

lemma height_mixed_square_root {f : ℝ → ℂ} (hf : Continuous f)
    {T K D E a b : ℝ} (hT : 0 < T) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsq : dyadicHeightMean (fun t => ‖f t‖^2) T ≤ K*(D*b+E)*a) :
    dyadicHeightMean (fun t => ‖f t‖) T ≤
      2*Real.sqrt K*(Real.sqrt D*Real.sqrt b+Real.sqrt E)*Real.sqrt a := by
  have hh := height_cell_square_root hf hT hK (mul_nonneg hD hb) hE ha
    (by norm_num : (0:ℝ) ≤ 1) (by simpa only [mul_one] using hsq)
  simpa only [Real.sqrt_one,mul_one,Real.sqrt_mul hD] using hh

end CubicFirstMoment

end

end OAI
