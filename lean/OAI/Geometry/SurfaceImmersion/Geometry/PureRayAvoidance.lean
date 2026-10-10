import OAI.Geometry.SurfaceImmersion.Primitive.CompactCrossingPreservation

namespace OAI

/-! Quantitative avoidance of the nonpositive first-axis ray for all nonzero
tangent directions, including directions whose first coordinate vanishes. -/
noncomputable section
namespace ClosedSurfaceR4.GeometryPreservation

lemma slope_first_positive {S D N L k t K : ℝ} (hS : 0 < S)
    (hk : -K ≤ k) (hN : K < N^2) : 0 < (slopePure S D N L k t).1 := by
  change 0 < (N^2+k+(D+S*t)^2)/S
  exact div_pos (by nlinarith [sq_nonneg (D+S*t)]) hS

lemma slope_ray_avoidance_longitudinal {sLo S D N L k t K d B : ℝ}
    (hmin : 0 < sLo) (hS : sLo ≤ S) (hK : 0 ≤ K) (hk : -K ≤ k)
    (hd : |D| ≤ d) (hB : 0 ≤ B) (hN : |N| ≤ B)
    (hL : 2*B*((Real.sqrt K+d)/sLo) < |L|) :
    0 < (slopePure S D N L k t).1 ∨ (slopePure S D N L k t).2 ≠ 0 := by
  by_cases hp : 0 < (slopePure S D N L k t).1
  · exact Or.inl hp
  · right
    intro hz
    have hSpos : 0 < S := hmin.trans_le hS
    have hnum : N^2+k+(D+S*t)^2 ≤ 0 := by
      have hh : (N^2+k+(D+S*t)^2)/S ≤ 0 := le_of_not_gt hp
      simpa only [zero_mul] using (div_le_iff₀ hSpos).mp hh
    have hsq : (D+S*t)^2 ≤ K := by nlinarith [sq_nonneg N]
    have hsqrt := Real.sq_sqrt hK
    have habs : |D+S*t| ≤ Real.sqrt K := by
      apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
      simpa only [sq_abs,hsqrt] using hsq
    have hSt : S*|t| ≤ Real.sqrt K+d := by
      have hh := abs_sub_le (D+S*t) 0 D
      simp only [sub_zero,zero_sub,abs_neg,add_sub_cancel_left,abs_mul,abs_of_pos hSpos] at hh
      linarith
    have ht : |t| ≤ (Real.sqrt K+d)/sLo := by
      apply (le_div_iff₀ hmin).mpr
      nlinarith [mul_le_mul_of_nonneg_right hS (abs_nonneg t)]
    have hLt : L = -(2*N*t) := by
      change L+2*N*t = 0 at hz
      linarith
    have hprod : |L| ≤ 2*B*((Real.sqrt K+d)/sLo) := by
      rw [hLt,abs_neg,abs_mul,abs_mul]
      norm_num only [show |(2 : ℝ)| = 2 by norm_num]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hN (by norm_num)) ht
        (abs_nonneg _) (by positivity)
    linarith

lemma pure_slope_scale {S D N L k b t : ℝ} (hS : S ≠ 0) :
    pureComponents S D N L k b (b*t) = b^2 • slopePure S D N L k t := by
  ext <;> dsimp [pureComponents,frameXX,frameXY,frameYY,slopePure] <;>
    field_simp <;> ring

lemma pure_vertical_positive {S D N L k c : ℝ} (hS : 0 < S) (hc : c ≠ 0) :
    0 < (pureComponents S D N L k 0 c).1 := by
  have h := pure_first_identity (D := D) (N := N) (L := L) (k := k)
    (b := 0) (c := c) hS.ne'
  have hsq : 0 < (S*c)^2 := sq_pos_of_ne_zero (mul_ne_zero hS.ne' hc)
  simp only [mul_zero,zero_add,zero_pow (by norm_num : 2 ≠ 0),mul_zero,add_zero] at h
  nlinarith

lemma pure_ray_avoidance_of_slopes {S D N L k b c : ℝ} (hS : 0 < S)
    (hv : b ≠ 0 ∨ c ≠ 0)
    (hslopes : ∀ t : ℝ, 0 < (slopePure S D N L k t).1 ∨
      (slopePure S D N L k t).2 ≠ 0) :
    0 < (pureComponents S D N L k b c).1 ∨
      (pureComponents S D N L k b c).2 ≠ 0 := by
  by_cases hb : b = 0
  · subst b
    exact Or.inl (pure_vertical_positive hS (hv.resolve_left (by simp)))
  · have hc : b*(c/b) = c := by field_simp
    rw [← hc,pure_slope_scale hS.ne']
    rcases hslopes (c/b) with hp | hz
    · exact Or.inl (mul_pos (sq_pos_of_ne_zero hb) hp)
    · exact Or.inr (mul_ne_zero (pow_ne_zero 2 hb) hz)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
