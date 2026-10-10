import OAI.Geometry.IsometricImmersion.Metric
import OAI.Geometry.IsometricImmersion.Immersions.FiniteHeight

namespace OAI

noncomputable section
open scoped ContDiff BigOperators
namespace SmoothLocal.Geometry

theorem height_smooth {F : Coord → Ambient} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (e : Ambient) :
    ContDiffOn ℝ ∞ (height F e) U :=
  hF.inner ℝ contDiffOn_const

def IsUnitNormalAt (F : Coord → Ambient) (e : Ambient) (p : Coord) : Prop :=
  inner ℝ e e = 1 ∧ ∀ v, inner ℝ (fderiv ℝ F p v) e = 0

theorem height_derivative_at_normal {F : Coord → Ambient} {U : Set Coord}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    {e : Ambient} (he : IsUnitNormalAt F e p) :
    fderiv ℝ (height F e) p = 0 := by
  exact height_differential_zero
    (((hF p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)) e he.2

theorem covHessian_height_at_normal (g : MetricField) {F : Coord → Ambient}
    {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) {e : Ambient} (he : IsUnitNormalAt F e p) :
    covHessian g (height F e) p = secondFundamental F e p := by
  have hz : ∀ k, coordPartial k (height F e) p = 0 := by
    intro k
    simp only [coordPartial, height_derivative_at_normal hF hU hp he,
      zero_apply]
  ext i j
  simp only [covHessian, hz, mul_zero, Finset.sum_const_zero, sub_zero,
    secondFundamental]
  exact second_partial_height hF hU hp e i j

def normalResidual (g : MetricField) (F : Coord → Ambient) (p : Coord) :
    Fin 2 → Fin 2 → Ambient := fun i j =>
  coordPartial i (coordPartial j F) p - ∑ k, christoffel g k i j p • coordPartial k F p

theorem covHessian_height_eq_residual (g : MetricField) {F : Coord → Ambient}
    {U : Set Coord} (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (e : Ambient) (i j : Fin 2) :
    covHessian g (height F e) p i j = inner ℝ (normalResidual g F p i j) e := by
  exact hessian_height_eq_residual_inner hF hU hp e (fun k i j => christoffel g k i j p) i j

end SmoothLocal.Geometry

end

end OAI
