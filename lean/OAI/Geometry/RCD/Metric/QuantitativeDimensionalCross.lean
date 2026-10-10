import OAI.Geometry.RCD.Coordinates.BochnerFrameCompletion

namespace OAI

/-! # Quantitative completion from the scalar dimensional inequality

The trace and squared norm of an almost orthonormal frame suffice.
No invertibility or independently postulated tangent dimension is used.
-/

open Real
noncomputable section
namespace RegularPointCoordinates

theorem dimensional_cross_defect {N A B r s D : ℝ}
    (hN : 1≤N) (hD : 0≤D) (hD1 : D≤1)
    (hA : |A-N|≤D) (hB : |B-N|≤D)
    (h : ∀ t : ℝ, (A+t*r)^2≤N*(B+2*t*s+t^2*r^2)) :
    (r-s)^2≤6*D*r^2 := by
  have hquad (t : ℝ) : 0≤((N-1)*r^2)*(t*t)+(2*N*s-2*A*r)*t+(N*B-A^2) := by
    have hh := h t
    nlinarith only [hh]
  have hd := discrim_le_zero hquad
  simp only [discrim] at hd
  have hcross : (N*s-A*r)^2≤(N-1)*r^2*(N*B-A^2) := by
    nlinarith only [hd]
  have hA' := abs_le.mp hA
  have hB' := abs_le.mp hB
  have htrace : N*B-A^2≤3*N*D := by
    nlinarith [sq_nonneg (A-N)]
  have hsmall : (A-N)^2≤D := by
    have hh : (A-N)^2≤D^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hD).mpr hA
    nlinarith
  have hc : (N*s-A*r)^2≤3*N*(N-1)*D*r^2 := by
    have hh := mul_le_mul_of_nonneg_left htrace
      (mul_nonneg (sub_nonneg.mpr hN) (sq_nonneg r))
    nlinarith only [hcross,hh]
  have hs : (A-N)^2*r^2≤D*r^2 := mul_le_mul_of_nonneg_right hsmall (sq_nonneg r)
  have hsum : N^2*(r-s)^2≤2*(N*s-A*r)^2+2*(A-N)^2*r^2 := by
    nlinarith only [sq_nonneg ((N*s-A*r)-(A-N)*r)]
  have hcoef : 6*N*(N-1)+2≤6*N^2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hD (sq_nonneg r))
  have hall : N^2*(r-s)^2≤N^2*(6*D*r^2) := by
    nlinarith only [hsum,hc,hs,hb]
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos (by linarith : 0<N))).mp hall

theorem dimensional_cross_abs_defect {N A B r s D : ℝ}
    (hN : 1≤N) (hD : 0≤D) (hD1 : D≤1)
    (hA : |A-N|≤D) (hB : |B-N|≤D)
    (h : ∀ t : ℝ, (A+t*r)^2≤N*(B+2*t*s+t^2*r^2)) :
    |r-s|≤√(6*D)*|r| := by
  have hh := dimensional_cross_defect hN hD hD1 hA hB h
  have hroot : (√(6*D)*|r|)^2=6*D*r^2 := by
    rw [mul_pow,Real.sq_sqrt (mul_nonneg (by norm_num) hD),sq_abs]
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (sqrt_nonneg _) (abs_nonneg _))).mp
  simpa only [sq_abs,hroot] using hh

end RegularPointCoordinates

end

end OAI
