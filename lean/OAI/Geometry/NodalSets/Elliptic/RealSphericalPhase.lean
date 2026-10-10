import OAI.Geometry.NodalSets.Elliptic.RealConvexifiedQuadraticLemmas

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section

lemma realCoordinateSquare_partial (y x : Yau.Jets.Coord) (i : Fin 4) :
    Yau.coordPartial (realCoordinateSquare y) x i = 2*(x i-y i) := by
  have hf (j : Fin 4) : ContDiff ℝ ∞ (fun z : Yau.Jets.Coord ↦ z j-y j) :=
    (contDiff_apply ℝ ℝ j).sub contDiff_const
  have hp (j : Fin 4) : Yau.coordPartial (fun z : Yau.Jets.Coord ↦ z j-y j) x i = (Pi.single i (1:ℝ) : Yau.Jets.Coord) j := by
    have hh := ((ContinuousLinearMap.proj j : Yau.Jets.Coord →L[ℝ] ℝ).hasFDerivAt (x := x) |>.sub_const (y j)).fderiv
    change fderiv ℝ (fun z : Yau.Jets.Coord ↦ z j-y j) x = ContinuousLinearMap.proj j at hh
    unfold Yau.coordPartial
    rw [hh]
    rfl
  have he : realCoordinateSquare y = fun z ↦ ∑ j, (z j-y j)*(z j-y j) := by
    funext z; simp [realCoordinateSquare,pow_two]
  rw [he,Yau.real_coordPartial_sum _ (fun j ↦ (hf j).mul (hf j))]
  simp_rw [Yau.real_coordPartial_mul _ _ (hf _) (hf _),hp]
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hji; simp [hji]
  · simp

lemma realCoordinateSquare_pos (y x : Yau.Jets.Coord) (hx : x ≠ y) : 0 < realCoordinateSquare y x :=
  (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hx))).trans_le (realCoordinateSquare_norm y x)

lemma realSphericalPhase_gradient (y x : Yau.Jets.Coord) (c : ℝ) :
    realCoordGradient (fun z ↦ c-realCoordinateSquare y z) x = fun i ↦ -2*(x i-y i) := by
  ext i
  unfold realCoordGradient Yau.coordPartial
  rw [fderiv_fun_sub (differentiableAt_const c) ((realCoordinateSquare_smooth y).differentiable (by simp) x)]
  simp only [fderiv_fun_const,Pi.zero_apply,zero_sub]
  have hh := realCoordinateSquare_partial y x i
  simp only [Yau.coordPartial] at hh
  change -(fderiv ℝ (realCoordinateSquare y) x (Pi.single i 1)) = _
  rw [hh]
  ring

lemma realSphericalPhase_gradient_ne_zero (y x : Yau.Jets.Coord) (c : ℝ) (hx : x ≠ y) :
    realCoordGradient (fun z ↦ c-realCoordinateSquare y z) x ≠ 0 := by
  rw [realSphericalPhase_gradient]
  intro hh
  apply hx
  ext i
  have hi := congrFun hh i
  change -2*(x i-y i)=0 at hi
  linarith

end
end Yau.Geometry

end OAI
