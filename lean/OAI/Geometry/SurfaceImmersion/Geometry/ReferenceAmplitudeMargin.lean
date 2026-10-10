import OAI.Geometry.SurfaceImmersion.Atlas.ReferenceCoordinateData
import OAI.Geometry.SurfaceImmersion.Primitive.BoundedPrimitiveAmplitude

namespace OAI

/-! One fixed parameter derivative bound for all active reference charts. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance amplitudeMarginFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance amplitudeMarginFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

theorem amplitude_parameter_margin : ∃ eps R : ℝ, 0 < eps ∧ 1 ≤ R ∧
    ∀ i p, p ∈ tsupport (d.B.weight i) → ∀ a : d.B.centers × Fin 3,
      p ∈ tsupport (d.B.weight a.1) → ∀ z : PrimitiveAmplitudeData (d.B.centers × Fin 3),
      ‖z-d.coordinateReference i p‖ < eps →
        (primitiveDataOperator z.1).IsInvertible ∧
        0 < primitiveParameterCoefficient a z ∧
        |primitiveParameterAmplitude a z| ≤ R ∧
        ‖fderiv ℝ (primitiveParameterAmplitude a) z‖ ≤ R := by
  classical
  obtain ⟨D,hD,hbound⟩ := d.coordinateReference_bound
  obtain ⟨k,hk,hlower⟩ := d.coefficient_lower
  choose eps R heps hR hnear using fun a : d.B.centers × Fin 3 =>
    bounded_primitive_amplitude_C1 a D hk
  obtain ⟨eta,heta,hle⟩ := finite_positive_lower heps
  let Q : ℝ := 1+∑ a, R a
  have hsum := Finset.sum_nonneg (s := Finset.univ) (fun a _ => zero_le_one.trans (hR a))
  refine ⟨eta,Q,heta,by dsimp only [Q]; linarith,?_⟩
  intro i p hp a ha z hz
  have hcoeff : k ≤ (d.coordinateReference i p).1.1.1 a (d.coordinateReference i p).2 := by
    rw [d.coordinateReference_coefficient i a hp ha]
    exact hlower a p ha
  obtain ⟨hi,hpos,_,_,hv,hd⟩ := hnear a (d.coordinateReference i p) (hbound i p hp)
    (d.coordinateReference_identity i hp) hcoeff z (hz.trans_le (hle a))
  have hRQ : R a ≤ Q := by
    have hh := Finset.single_le_sum (fun b _ => zero_le_one.trans (hR b)) (Finset.mem_univ a)
    dsimp only [Q]; linarith
  exact ⟨hi,hpos,hv.trans hRQ,hd.trans hRQ⟩

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
