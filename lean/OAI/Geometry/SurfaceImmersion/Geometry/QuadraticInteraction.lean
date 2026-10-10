import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateTaylorIdentity

namespace OAI

/-! Separate the mixed and pure terms introduced by the second, forced
correction from the quadratic tensor of the first, free correction. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

def coordinateQuadraticInteraction {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) (X Y : RealModes.RField 4) : SmallModes.Base → PhaseMean.Tensor :=
  fun p k => RealModes.realLinearizedTensor X Y p k + RealModes.realMetricTensor Y p k +
    (∑ l, ε ^ (l.val + 1) * (1 / 2 : ℝ) *
      (((P k l).variations 1).eval ![G, X ∘ planeCoordinateIsometry, Y ∘ planeCoordinateIsometry, 0]
        (planeCoordinateIsometry.symm p,0) +
       ((P k l).variations 1).eval ![G, Y ∘ planeCoordinateIsometry, X ∘ planeCoordinateIsometry, 0]
        (planeCoordinateIsometry.symm p,0))) +
    coordinateQuadraticPolynomial P ε G Y 0 p k

lemma coordinateFullLinearized_add {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) {X Y : RealModes.RField 4}
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) :
    coordinateFullLinearized P ε G (X + Y) =
      coordinateFullLinearized P ε G X + coordinateFullLinearized P ε G Y := by
  have ha : X + Y = (fun x => X x + Y x) := rfl
  have hc : (X + Y) ∘ planeCoordinateIsometry =
      (fun x => (X ∘ planeCoordinateIsometry) x + (Y ∘ planeCoordinateIsometry) x) := rfl
  funext p k
  simp only [coordinateFullLinearized, Pi.add_apply, coordinateRealLinearized,
    RealModes.realLinearizedTensor_apply]
  rw [hc, linearized_add _ ε G (hX.comp planeCoordinateIsometry.contDiff)
    (hY.comp planeCoordinateIsometry.contDiff), ha,
    RealModes.realLinearized_add_right (hX.differentiable (by simp) p) (hY.differentiable (by simp) p)]
  ring

lemma coordinateFullQuadratic_add {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    (G : Base → Space) {X Y : RealModes.RField 4}
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) :
    coordinateFullQuadratic P ε G (X + Y) =
      coordinateFullQuadratic P ε G X + coordinateQuadraticInteraction P ε G X Y := by
  have hx := hX.comp planeCoordinateIsometry.contDiff
  have hy := hY.comp planeCoordinateIsometry.contDiff
  have ha : X + Y = (fun x => X x + Y x) := rfl
  have hc : (X + Y) ∘ planeCoordinateIsometry =
      (fun x => (X ∘ planeCoordinateIsometry) x + (Y ∘ planeCoordinateIsometry) x) := rfl
  funext p k
  simp only [coordinateFullQuadratic, Pi.add_apply, coordinateQuadraticInteraction]
  rw [ha, RealModes.realMetricTensor_add (hX.differentiable (by simp) p) (hY.differentiable (by simp) p)]
  simp only [Pi.add_apply, coordinateQuadraticPolynomial]
  rw [← ha, hc]
  simp_rw [real_second_variation_add_left _ G hx hy,
    real_second_variation_add_right _ G _ hx hy]
  simp only [mul_add, Finset.sum_add_distrib]
  ring_nf

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
