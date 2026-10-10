import OAI.Geometry.RCD.Metric.ApproximationRestriction

namespace OAI

/-! # Changing the physical unit in a pointed Euclidean approximation -/

open Metric
noncomputable section
namespace RegularPointCoordinates

theorem IsPointedApproximation.rescale_unit {X : Type*} [MetricSpace X] {n : ℕ}
    {p : X} {r S ε : ℝ} (hr : 0 < r) (hS : 0 < S) {f : X → Euclidean n}
    (hf : IsPointedApproximation p 0 (S*r) 1 ε f) :
    IsPointedApproximation p 0 r S (S*ε) (fun x => S • f x) := by
  have hd (v w : Euclidean n) : dist (S • v) (S • w) = S*dist v w := by
    rw [dist_smul₀,Real.norm_of_nonneg hS.le]
  refine ⟨?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hf.1 hS.le
    simpa only [← hd,smul_zero] using hh
  · intro x y hx hy
    have hh := mul_le_mul_of_nonneg_left
      (hf.2.1 x y (by simpa only [one_mul] using hx) (by simpa only [one_mul] using hy)) hS.le
    have he : S*(dist (f x) (f y)-dist x y/(S*r)) =
        dist (S • f x) (S • f y)-dist x y/r := by rw [hd]; field_simp
    have hh' : |S*(dist (f x) (f y)-dist x y/(S*r))| ≤ S*ε := by
      rw [abs_mul,abs_of_pos hS]
      exact hh
    rwa [he] at hh'
  · intro y hy
    have hy' : dist (S⁻¹ • y) 0 ≤ 1-ε := by
      rw [dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hS).le]
      have hh : ‖y‖ ≤ S*(1-ε) := by
        simpa only [dist_zero_right,mul_sub,mul_one] using hy
      have hm := mul_le_mul_of_nonneg_left hh (inv_pos.mpr hS).le
      simpa only [← mul_assoc,inv_mul_cancel₀ hS.ne',one_mul] using hm
    obtain ⟨x,hx,hxy⟩ := hf.2.2 (S⁻¹ • y) hy'
    refine ⟨x,by simpa only [one_mul] using hx,?_⟩
    have hh := mul_le_mul_of_nonneg_left hxy hS.le
    rw [← hd,smul_smul,mul_inv_cancel₀ hS.ne',one_smul] at hh
    exact hh

end RegularPointCoordinates

end

end OAI
