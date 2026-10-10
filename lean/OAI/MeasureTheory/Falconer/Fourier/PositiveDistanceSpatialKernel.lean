import OAI.MeasureTheory.Falconer.Geometry.PositiveDistanceBins

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem width_kernel (d : PositiveDistanceData) (z : ℝ × ℝ) :
    1/(1+|z.1-z.2|/d.width)^2 = 1/(1+(2:ℝ)^d.t*|z.1-z.2|)^2 := by
  simp only [width,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
    Real.rpow_natCast,div_eq_mul_inv,inv_inv,mul_comm]

theorem normalization_congr (d e : PositiveDistanceData)
    (hN : d.N = e.N) (ha : d.a = e.a) (ht : d.t = e.t)
    (hm : d.mass d.a = e.mass e.a) : d.normalization = e.normalization := by
  simp only [normalization,levelMass,hN,ha,ht] at *
  rw [hm]

theorem spatial_kernel_max (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (ht : d.t = e.t) (hn : d.normalization = e.normalization)
    (S : Set ((Plane × Plane) × (Plane × Plane))) :
    (∫⁻ z in S, ENNReal.ofReal
      (1/(1+(2:ℝ)^d.t*|dist z.1.1 z.1.2-dist z.2.1 z.2.2|)^2)
      ∂d.pair.prod e.pair) ≤
      binKernelConstant * ENNReal.ofReal
        (d.levelMass^4*(2:ℝ)^(-((d.t:ℝ)-d.a))) * max d.coincidence e.coincidence := by
  let F : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (1/(1+(2:ℝ)^d.t*|z.1-z.2|)^2)
  have hF : Measurable F := by unfold F; fun_prop
  apply (d.lintegral_drop_extra_restriction e F hF S).trans
  have he : F = fun z => ENNReal.ofReal (1/(1+|z.1-z.2|/d.width)^2) := by
    funext z
    rw [d.width_kernel]
  rw [he]
  exact common_profile_distance_kernel_max d e ht hn

theorem spatial_stationary_kernel_max (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (ht : d.t = e.t) (hn : d.normalization = e.normalization)
    (S : Set ((Plane × Plane) × (Plane × Plane))) :
    ENNReal.ofReal ((2:ℝ)^(-((d.t:ℝ)-d.a))) *
      (∫⁻ z in S, ENNReal.ofReal
        (1/(1+(2:ℝ)^d.t*|dist z.1.1 z.1.2-dist z.2.1 z.2.2|)^2)
        ∂d.pair.prod e.pair) ≤
      binKernelConstant * ENNReal.ofReal
        (d.levelMass^4*(2:ℝ)^(-2*((d.t:ℝ)-d.a))) * max d.coincidence e.coincidence := by
  have hh := mul_le_mul_right (spatial_kernel_max d e ht hn S)
    (ENNReal.ofReal ((2:ℝ)^(-((d.t:ℝ)-d.a))))
  have he : (2:ℝ)^(-((d.t:ℝ)-d.a)) *
      (d.levelMass^4*(2:ℝ)^(-((d.t:ℝ)-d.a))) =
      d.levelMass^4*(2:ℝ)^(-2*((d.t:ℝ)-d.a)) := by
    rw [mul_left_comm,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 2
    ring
  have hc (x y z w : ℝ≥0∞) : x*(y*z*w) = y*(x*z)*w := by ring
  rw [hc,← ENNReal.ofReal_mul (by positivity),he] at hh
  exact hh

end PositiveDistanceData

end PlanarFalconer

end OAI
