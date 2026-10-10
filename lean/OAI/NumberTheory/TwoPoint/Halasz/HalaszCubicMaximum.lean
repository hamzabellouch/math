import OAI.NumberTheory.TwoPoint.Halasz.HalaszCubicLaplace

namespace OAI

/-! Cubic logarithmic cancellation absorbs a strip displacement. -/
namespace TwoPointCorrelations

lemma halasz_cubic_maximum {δ y L : ℝ} (hδ : 0≤δ) (hy : 0≤y) (hL : 0<L) :
    δ*y-y^3/((10^15:ℝ)*L^2)≤(10^9:ℝ)*δ^(3/2:ℝ)*L := by
  have hh := halasz_cubic_balance hδ hy (show 0<(10^6:ℝ)*L by positivity)
  have he : (1000:ℝ)*((10^6:ℝ)*L)^2=(10^15:ℝ)*L^2 := by ring
  rw [he] at hh
  have hn : 0≤y^3/(2000*((10^6:ℝ)*L)^2) := by positivity
  nlinarith

lemma halasz_log_cubic_identity {N L lam : ℝ} (hL : 0<L)
    (hy : 0<Real.log N) (hLlam : L=lam*Real.log N) :
    (-1/((10^15:ℝ)*lam^2))*Real.log N =
      -(Real.log N)^3/((10^15:ℝ)*L^2) := by
  have hlam : 0<lam := by nlinarith
  rw [hLlam]
  field_simp

end TwoPointCorrelations

end OAI
