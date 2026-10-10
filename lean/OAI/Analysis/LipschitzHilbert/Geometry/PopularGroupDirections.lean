import OAI.Analysis.LipschitzHilbert.Fourier.ProjectionFiberGeometry

namespace OAI

/-! Directions in one overlapping projected-popularity group are close.
This uses actual popularity points with the same long coordinate. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace LipschitzHilbert.Rectangle

theorem popular_group_directions (S R T : Rectangle) {v : Plane → Plane} {K : ℝ≥0}
    (hv : LipschitzWith K v) (hu : ∀ x, ‖v x‖ = 1)
    (hscale : 100*(K:ℝ)*S.long ≤ 1) (hRS : R.long ≤ S.long) (hTR : T.long ≤ R.long)
    (hR : (R.carrier ∩ S.carrier).Nonempty) (hT : (T.carrier ∩ S.carrier).Nonempty)
    (hRw : 64*R.short ≤ R.long*dist (S.axes 0) (R.axes 0))
    (hTw : 64*T.short ≤ T.long*dist (S.axes 0) (T.axes 0))
    (hSw : 32*S.short ≤ S.long*dist (S.axes 0) (R.axes 0))
    {x y : Plane} (hx : x ∈ R.popularSet v) (hy : y ∈ T.popularSet v)
    (hxy : (S.orthogonalCoordinates x).1 = (S.orthogonalCoordinates y).1) :
    dist (R.axes 0) (T.axes 0) ≤ dist (S.axes 0) (R.axes 0)/2 := by
  let θ := dist (S.axes 0) (R.axes 0)
  let φ := dist (S.axes 0) (T.axes 0)
  let d := dist (R.axes 0) (T.axes 0)
  have hθ : 0 ≤ θ := dist_nonneg
  have hφ : 0 ≤ φ := dist_nonneg
  have hφd : φ ≤ θ+d := dist_triangle _ _ _
  have hRsmall : R.short ≤ R.long*θ := by dsimp [θ]; nlinarith [R.short_pos]
  have hTsmall : T.short ≤ T.long*φ := by dsimp [φ]; nlinarith [T.short_pos]
  have hφlen : T.long*φ ≤ R.long*φ := mul_le_mul_of_nonneg_right hTR hφ
  have hdist0 := S.shared_projection_distance R T x y hx.1 hy.1 hR hT hxy
  have hdist : dist x y ≤ S.short+2*R.long*(θ+φ) := by
    change dist x y ≤ S.short+R.long*θ+R.short+T.long*φ+T.short at hdist0
    nlinarith
  have hKl : (K:ℝ)*R.long ≤ 1/100 := by
    have h := mul_le_mul_of_nonneg_left hRS K.coe_nonneg
    nlinarith
  have hKθ : (K:ℝ)*S.long*θ ≤ θ/100 := by
    have h := mul_le_mul_of_nonneg_right hscale hθ
    nlinarith
  have hKS : (K:ℝ)*S.short ≤ θ/3200 := by
    have h := mul_le_mul_of_nonneg_left hSw K.coe_nonneg
    change (K:ℝ)*(32*S.short) ≤ (K:ℝ)*(S.long*θ) at h
    nlinarith
  have hKsum : (K:ℝ)*R.long*(θ+φ) ≤ (θ+φ)/100 := by
    have h := mul_le_mul_of_nonneg_right hKl (add_nonneg hθ hφ)
    nlinarith
  have hKdist : (K:ℝ)*dist x y ≤ θ/3200+(θ+φ)/50 := by
    have h := mul_le_mul_of_nonneg_left hdist K.coe_nonneg
    nlinarith
  have hRap : R.short/(2*R.long) ≤ θ/128 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) R.long_pos)).mpr
    change 64*R.short ≤ R.long*θ at hRw
    nlinarith
  have hTap : T.short/(2*T.long) ≤ φ/128 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) T.long_pos)).mpr
    change 64*T.short ≤ T.long*φ at hTw
    nlinarith
  have hvxy := hv.dist_le_mul x y
  have hxv := R.popular_axis_distance hu hx
  have hyv := T.popular_axis_distance hu hy
  have ht1 := dist_triangle (R.axes 0) (v x) (T.axes 0)
  have ht2 := dist_triangle (v x) (v y) (T.axes 0)
  rw [dist_comm (R.axes 0) (v x)] at ht1
  change d ≤ _ at ht1
  change dist (v x) (R.axes 0) ≤ R.short/(2*R.long) at hxv
  nlinarith

end LipschitzHilbert.Rectangle

end

end OAI
