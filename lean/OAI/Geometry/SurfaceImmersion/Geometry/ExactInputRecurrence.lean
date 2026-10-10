import OAI.Geometry.SurfaceImmersion.Geometry.GlobalInputRecurrence
import OAI.Geometry.SurfaceImmersion.Geometry.ExactInputRecurrenceBound
import OAI.Geometry.SurfaceImmersion.Geometry.ExactScaleOrdering

namespace OAI

/-! The actual next map and normalized defect satisfy the waiting recurrence. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance exactInputFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance exactInputFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exact_scale_input_recurrence {g : SmoothMetric M} {G U : M → Space}
    (hG : ContMDiff planeModel spaceModel ∞ G) (hU : ContMDiff planeModel spaceModel ∞ U)
    {t P P₀ Pm B C L B₀ δ' : ℝ} {k m : ℕ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hk : 10 ≤ k)
    (hP : 0 ≤ P) (hP₀ : 0 ≤ P₀) (hPm : 0 ≤ Pm)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 ≤ L) (hB₀ : 0 ≤ B₀)
    (hp : A.ShiftedBound 2 0 t P G)
    (hc : A.ShiftedBound 2 m t C G)
    (hu : A.WeightedBound (t^(6/5 : ℝ)) (2+m) (B*(t^(k : ℝ)*t^(6/5 : ℝ))) U)
    (ht₀ : A.TensorWeightedBound 1 0 P₀ g.inner)
    (htm : A.TensorWeightedBound 1 m Pm g.inner)
    (he : A.TensorWeightedBound (t^(6/5 : ℝ)) m (L*(1+B₀+C)*t^(1/5 : ℝ))
      (normalizedTensorDefect g.inner δ' (G+U)-g.inner)) :
    A.InputBound (t^(6/5 : ℝ)) m
      (P+P₀+(Pm+B+L*(1+B₀)+1+L)*t^(1/5 : ℝ)*(1+C))
      (G+U) (normalizedTensorDefect g.inner δ' (G+U)) := by
  have hτ : 0 < t^(6/5 : ℝ) := Real.rpow_pos_of_pos ht _
  obtain ⟨_,_,hτs,hst⟩ := ExactCorrection.exact_scale_order ht ht1 hk
  have hτt := hτs.trans hst
  have hh := A.next_input_bound g.contMDiff hG hU ht hτ hτt (hτt.trans ht1)
    hP hP₀ hPm hC (mul_nonneg hB (mul_nonneg (Real.rpow_nonneg ht.le _) hτ.le))
    (mul_nonneg (mul_nonneg hL (by linarith)) (Real.rpow_nonneg ht.le _))
    hp hc hu ht₀ htm he
  have hsize := ExactCorrection.exact_input_recurrence_bound ht ht1 hk hPm hB hC hL hB₀
    (P := P) (P₀ := P₀)
  constructor
  · intro i j hj x
    exact (hh.1 i j hj x).trans hsize
  · intro i
    exact (hh.2 i).mono_const hsize

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
