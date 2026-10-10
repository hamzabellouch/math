import OAI.MeasureTheory.Falconer.Estimates.CommonTubePacking
import OAI.MeasureTheory.Falconer.Estimates.CommonTubePower

namespace OAI

/-! Interpolation of the regularity and separation bounds on a common
pencil. The intermediate potential exponent stays strictly below the point
dimension, so only the already proved finite geometric-series bound is used. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem interpolate_two_power_bounds {z A B r s u θ : ℝ}
    (hz : 0 ≤ z) (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 < r)
    (hθ : 0 < θ) (hθ1 : θ < 1) (he : s*θ+2*(1-θ) = u)
    (hfirst : z ≤ A*r^s) (hsecond : z ≤ B*r^2) :
    z ≤ A^θ*B^(1-θ)*r^u := by
  by_cases hz0 : z = 0
  · rw [hz0]
    positivity
  have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
  calc
    z = z^θ*z^(1-θ) := by rw [← Real.rpow_add hzpos]; norm_num
    _ ≤ (A*r^s)^θ*(B*r^2)^(1-θ) := by
      exact mul_le_mul (Real.rpow_le_rpow hz hfirst hθ.le)
        (Real.rpow_le_rpow hz hsecond (by linarith only [hθ1]))
        (Real.rpow_nonneg hz _) (by positivity)
    _ = A^θ*B^(1-θ)*r^u := by
      rw [Real.mul_rpow hA (Real.rpow_nonneg hr.le _),
        Real.mul_rpow hB (sq_nonneg r),← Real.rpow_mul hr.le,
        ← Real.rpow_natCast_mul hr.le 2 (1-θ)]
      norm_num only [Nat.cast_ofNat]
      rw [show A^θ*r^(s*θ)*(B^(1-θ)*r^(2*(1-θ))) =
        (A^θ*B^(1-θ))*(r^(s*θ)*r^(2*(1-θ))) by ring,
        ← Real.rpow_add hr,he]

theorem intersect_tube_interpolated_bound {δ s u θ K M : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (hθ : 0 < θ) (hθ1 : θ < 1) (he : s*θ+2*(1-θ) = u)
    (T U : Finset (Space 2)) (x y : Space 2) (hx0 : |x 0| ≤ 1)
    (hchart : InBoundedLineChart T) (hsep : FiniteSeparatedAt δ T)
    (hball : NormalizedFiniteBallBound δ s K T) (hM : (T.card:ℝ) ≤ M)
    (hx : ∀ l ∈ T, TubeIncident δ x l) (hy : ∀ l ∈ U, TubeIncident δ y l) :
    ((T ∩ U).card:ℝ) ≤
      (K*(80*δ)^s*M)^θ*(25921:ℝ)^(1-θ)*(1/truncatedPlanarDistance δ x y)^u := by
  have hr := (truncatedPlanarDistance_bounds hδ hδ1 x y).1
  have hm0 : 0 ≤ M := (Nat.cast_nonneg _).trans hM
  have hfirst : ((T ∩ U).card:ℝ) ≤
      (K*(80*δ)^s*M)*(1/truncatedPlanarDistance δ x y)^s := by
    have hh := intersect_tube_kernel_bound hδ hδ1 hs hK T U x y hx0 hchart hx hy hball
    rw [show 80*δ/truncatedPlanarDistance δ x y =
      (80*δ)*(1/truncatedPlanarDistance δ x y) by ring,
      Real.mul_rpow (by positivity : 0 ≤ 80*δ) (by positivity)] at hh
    calc
      _ ≤ _ := hh
      _ = (K*(80*δ)^s*(T.card:ℝ))*(1/truncatedPlanarDistance δ x y)^s := by ring
      _ ≤ _ := by gcongr
  exact interpolate_two_power_bounds (Nat.cast_nonneg _) (by positivity)
    (by norm_num) (by positivity) hθ hθ1 he hfirst
    (intersect_tube_packing_bound hδ hδ1 T U x y hx0 hchart hsep hx hy)

end Falconer

end OAI
