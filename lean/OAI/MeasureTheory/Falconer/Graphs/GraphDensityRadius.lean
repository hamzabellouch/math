import OAI.MeasureTheory.Falconer.Graphs.GraphDensity
import OAI.MeasureTheory.Falconer.Measures.ScalarDensityZoom

namespace OAI

/-! The planar exponent exceeds twice the scalar density exponent. Thus
retained graph degrees force a quantitative lower bound for the zoom radius. -/
namespace Falconer

 theorem scalar_density_graph_gap {R κ t C N m : ℝ}
    (hR : 0 < R) (hN : 0 < N)
    (hmass : (R/2)^κ*N ≤ m) (hrelative : (m/N)^2 ≤ C*R^t) :
    1 ≤ (2:ℝ)^(2*κ)*C*R^(t-2*κ) := by
  have hm : (R/2)^κ ≤ m/N := (le_div_iff₀ hN).2 hmass
  have hh := (pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) κ) hm 2).trans hrelative
  have he : ((R/2)^κ)^2 = R^(2*κ)/(2:ℝ)^(2*κ) := by
    rw [show 2*κ = κ+κ by ring,Real.rpow_add hR,
      Real.rpow_add (by norm_num : (0:ℝ)<2),Real.div_rpow hR.le (by norm_num)]
    ring
  rw [he] at hh
  have hraw := (div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (2*κ))).1 hh
  have heR : R^t = R^(t-2*κ)*R^(2*κ) := by
    rw [← Real.rpow_add hR]
    congr 1
    ring
  rw [heR] at hraw
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hR (2*κ))).1
  convert hraw using 1 <;> ring

 theorem scalar_graph_radius_lower {R β C : ℝ} (hR : 0 < R)
    (hβ : 0 < β) (hC : 0 < C) (hbound : 1 ≤ C*R^β) :
    (1/C)^(1/β) ≤ R := by
  have hh : 1/C ≤ R^β := (div_le_iff₀ hC).2 (by simpa only [mul_comm] using hbound)
  have hb := Real.rpow_le_rpow (by positivity : 0 ≤ 1/C) hh (by positivity : 0 ≤ 1/β)
  rwa [← Real.rpow_mul hR.le,mul_one_div_cancel hβ.ne',Real.rpow_one] at hb

end Falconer

end OAI
