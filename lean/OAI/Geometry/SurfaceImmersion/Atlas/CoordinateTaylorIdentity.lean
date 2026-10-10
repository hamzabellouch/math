import OAI.Geometry.SurfaceImmersion.Geometry.CombinedQuadraticExpansion
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialTaylorRemainder
import OAI.Geometry.SurfaceImmersion.Geometry.SecondVariationAlgebra

namespace OAI

/-! Exact Taylor identity for the metric plus its finite polynomial
perturbation, in the coordinates of the forced-mode construction. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

def coordinatePolynomialValue {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (t : ℝ) : SmallModes.Base → PhaseMean.Tensor :=
  fun p k => ∑ l, ε ^ (l.val + 1) * (P k l).eval G (planeCoordinateIsometry.symm p,t)

def coordinateMetricMap {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) : SmallModes.Base → PhaseMean.Tensor :=
  RealModes.realMetricTensor (G ∘ planeCoordinateIsometry.symm) + coordinatePolynomialValue P ε G 0

def coordinateFullQuadratic {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (X : RealModes.RField 4) : SmallModes.Base → PhaseMean.Tensor :=
  RealModes.realMetricTensor X + coordinateQuadraticPolynomial P ε G X 0

def coordinateTaylorRemainder {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (X : RealModes.RField 4) : SmallModes.Base → PhaseMean.Tensor :=
  fun p k => ∑ l, ε ^ (l.val + 1) *
    (P k l).taylorRemainder G (X ∘ planeCoordinateIsometry) 0 (planeCoordinateIsometry.symm p)

theorem coordinate_metric_taylor_identity {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (ε : ℝ) {G : Base → Space} {X : RealModes.RField 4}
    (hG : ContDiff ℝ ∞ G) (hX : ContDiff ℝ ∞ X) :
    coordinateMetricMap P ε (fun x => G x + X (planeCoordinateIsometry x)) -
      coordinateMetricMap P ε G =
      coordinateFullLinearized P ε G X + coordinateFullQuadratic P ε G X +
        coordinateTaylorRemainder P ε G X := by
  have hf : (fun x => G x + X (planeCoordinateIsometry x)) ∘ planeCoordinateIsometry.symm =
      fun p => (G ∘ planeCoordinateIsometry.symm) p + X p := by
    funext p
    simp only [Function.comp_apply, planeCoordinateIsometry.apply_symm_apply]
  funext p k
  simp only [coordinateMetricMap, Pi.sub_apply, Pi.add_apply, hf]
  rw [RealModes.realMetricTensor_add
    ((hG.comp planeCoordinateIsometry.symm.contDiff).differentiable (by simp) p)
    (hX.differentiable (by simp) p)]
  simp only [coordinateFullLinearized, coordinateRealLinearized, coordinateFullQuadratic,
    coordinateQuadraticPolynomial, coordinatePolynomialValue, coordinateTaylorRemainder,
    linearized, Pi.add_apply, Expression.taylorRemainder]
  simp only [second_diagonal_eq_pair _ hG (hX.comp planeCoordinateIsometry.contDiff),
    mul_sub, Finset.sum_sub_distrib, Function.comp_apply]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
