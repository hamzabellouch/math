import OAI.Geometry.IsometricImmersion.Immersions.ActualHeight
import OAI.Geometry.IsometricImmersion.Immersions.InducedMetric
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open scoped ContDiff BigOperators Matrix
namespace SmoothLocal.Geometry

def christoffelFirstKind (g : MetricField) (i j : Fin 2) (p : Coord) : Coord :=
  fun l => (coordPartial i (fun q => g q j l) p +
    coordPartial j (fun q => g q i l) p - coordPartial l (fun q => g q i j) p) / 2

theorem christoffel_eq_inverse_mulVec (g : MetricField) (i j : Fin 2) (p : Coord) :
    (fun k => christoffel g k i j p) = (g p)⁻¹ *ᵥ christoffelFirstKind g i j p := by
  ext k
  simp only [christoffel, inverseMetric, Matrix.mulVec, dotProduct, christoffelFirstKind]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem metric_mul_christoffel {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U) (i j : Fin 2) :
    g p *ᵥ (fun k => christoffel g k i j p) = christoffelFirstKind g i j p := by
  rw [christoffel_eq_inverse_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hg.2 p hp).isUnit),
    Matrix.one_mulVec]

theorem normalResidual_orthogonal_tangent {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (i j l : Fin 2) :
    inner ℝ (normalResidual g F p i j) (coordPartial l F p) = 0 := by
  have hind (a b : Fin 2) :
      inner ℝ (coordPartial a F p) (coordPartial b F p) = g p b a := by
    rw [real_inner_comm (coordPartial b F p) (coordPartial a F p)]
    exact congrFun (congrFun (inducedMetric_eq_of_isometric hF hp) b) a
  have hc := congrFun (metric_mul_christoffel hg hp i j) l
  have hc' : ∑ k, christoffel g k i j p * g p l k = christoffelFirstKind g i j p l := by
    simpa only [Matrix.mulVec, dotProduct, mul_comm] using hc
  simp only [normalResidual, inner_sub_left, sum_inner, real_inner_smul_left, hind]
  rw [hc', second_partial_inner_tangent hF hU hp]
  exact sub_self _

end SmoothLocal.Geometry

end

end OAI
