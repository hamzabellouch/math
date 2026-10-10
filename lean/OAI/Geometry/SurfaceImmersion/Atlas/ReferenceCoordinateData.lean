import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveCoordinateData
import OAI.Geometry.SurfaceImmersion.Geometry.ReferenceCoefficientLower
import OAI.Geometry.SurfaceImmersion.Geometry.ReferenceMetricStability

namespace OAI

/-! Size, identity and positivity of the fixed reference data in any active
chart. The constants precede every independent radius and phase choice. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance refDataFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance refDataFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance refDataDualNormed : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance refDataDualSpace : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance refDataDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance refDataDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance refDataSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance refDataSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

def coordinateReference (i : d.B.centers) (p : M) : PrimitiveAmplitudeData (d.B.centers × Fin 3) :=
  d.B.primitiveCoordinateData d.basis (fun a => d.B.weight a.1) d.globalPhases gref.inner i
    {a | p ∈ tsupport (d.B.weight a.1)} (chart (i : M) p)

omit [CompactSpace M] in
lemma coordinateReference_identity (i : d.B.centers) {p : M}
    (hp : p ∈ tsupport (d.B.weight i)) :
    primitiveDataOperator (d.coordinateReference i p).1 = ContinuousLinearMap.id ℝ TensorFiber := by
  classical
  unfold coordinateReference
  rw [d.B.primitiveCoordinateData_operator d.basis (fun a => d.B.weight a.1) d.globalPhases
    (fun a => d.B.curvedAtlasPhase_smooth d.localPhases
      (fun _ _ => PhaseGeometry.centeredConvexPhase_smooth _ _ _) a)
    gref.inner i {a | p ∈ tsupport (d.B.weight a.1)} (d.B.weight_support i hp)
    (fun a ha => image_eq_zero_of_notMem_tsupport ha),d.operator_identity]
  apply ContinuousLinearMap.ext
  intro H
  change (d.B.tensorTriv i).continuousLinearMapAt ℝ p ((d.B.tensorTriv i).symmL ℝ p H) = H
  exact (d.B.tensorTriv i).continuousLinearMapAt_symmL (R := ℝ)
    (d.B.tensorTriv_domain i (d.B.weight_support i hp)) H

omit [CompactSpace M] [T2Space M] in
lemma coordinateReference_coefficient (i : d.B.centers) (a : d.B.centers × Fin 3)
    {p : M} (hi : p ∈ tsupport (d.B.weight i)) (ha : p ∈ tsupport (d.B.weight a.1)) :
    (d.coordinateReference i p).1.1.1 a (d.coordinateReference i p).2 =
      d.B.primitiveCoefficientField d.basis a p (gref.inner p) := by
  classical
  unfold coordinateReference SmoothingAtlas.primitiveCoordinateData
  simp only [Set.mem_ofPred_eq,ite_eq_left ha]
  unfold SmoothingAtlas.coefficientFrameRead SmoothingAtlas.coefficientFrame
  rw [(chart (i : M)).left_inv (d.B.weight_support i hi)]
  change d.B.primitiveCoefficientField d.basis a p
    ((d.B.tensorTriv i).symmL ℝ p ((d.B.tensorTriv i).continuousLinearMapAt ℝ p (gref.inner p))) = _
  erw [(d.B.tensorTriv i).symmL_continuousLinearMapAt (d.B.tensorTriv_domain i (d.B.weight_support i hi))]

lemma coordinateReference_bound : ∃ D : ℝ, 1 ≤ D ∧ ∀ i p,
    p ∈ tsupport (d.B.weight i) → ‖d.coordinateReference i p‖ ≤ D := by
  classical
  obtain ⟨Dq,hDq,hq⟩ := d.B.coefficientFrame_bound d.basis
    (fun a _p hp => d.basis_smooth a.1 hp a.2)
  choose Dv hDv hv using fun a => d.B.covectorFrame_bound (d.globalPhases a)
    (d.B.curvedAtlasPhase_smooth d.localPhases (fun _ _ => PhaseGeometry.centeredConvexPhase_smooth _ _ _) a)
  choose H hH using fun i => (d.B.chartWeightCompact i).isCompact.exists_bound_of_continuousOn
    (d.chartReference_smooth i).continuous.continuousOn
  let D := 1+Dq+(∑ a, Dv a)+(∑ i, |H i|)
  have hsumv := Finset.sum_nonneg (s := Finset.univ) (fun a _ => zero_le_one.trans (hDv a))
  have hsumH := Finset.sum_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (H i))
  have hD : 1 ≤ D := by dsimp only [D]; linarith
  have hqD : Dq ≤ D := by dsimp only [D]; linarith
  have hvD (a : d.B.centers × Fin 3) : Dv a ≤ D := by
    have hh := Finset.single_le_sum (fun a _ => zero_le_one.trans (hDv a)) (Finset.mem_univ a)
    dsimp only [D]; linarith
  have hHD (i : d.B.centers) : H i ≤ D := by
    have hh := Finset.single_le_sum (fun i _ => abs_nonneg (H i)) (Finset.mem_univ i)
    have := le_abs_self (H i)
    dsimp only [D]; linarith
  refine ⟨D,hD,?_⟩
  intro i p hp
  have hs := d.B.weight_support i hp
  have hn : 0 ≤ D := zero_le_one.trans hD
  unfold coordinateReference SmoothingAtlas.primitiveCoordinateData
  simp only [(chart (i : M)).left_inv hs]
  apply max_le
  · apply max_le
    · apply max_le
      · apply (pi_norm_le_iff_of_nonneg hn).mpr
        intro a
        change ‖if p ∈ tsupport (d.B.weight a.1) then
          d.B.coefficientFrameRead d.basis i a (chart (i : M) p) else 0‖ ≤ D
        split_ifs with ha
        · change ‖d.B.coefficientFrame d.basis i a ((chart (i : M)).symm (chart (i : M) p))‖ ≤ D
          rw [(chart (i : M)).left_inv hs]
          exact (hq i a p hp ha).trans hqD
        · simpa only [norm_zero] using hn
      · apply (pi_norm_le_iff_of_nonneg hn).mpr
        intro a
        have hh := Finset.single_le_sum (fun b _ => sq_nonneg (d.B.weight b p)) (Finset.mem_univ a.1)
        rw [d.B.partition p] at hh
        have hab : |d.B.weight a.1 p| ≤ 1 := by nlinarith [sq_abs (d.B.weight a.1 p),abs_nonneg (d.B.weight a.1 p)]
        exact (show ‖d.B.weight a.1 p‖ ≤ 1 by simpa only [Real.norm_eq_abs] using hab).trans hD
    · apply (pi_norm_le_iff_of_nonneg hn).mpr
      intro a
      change ‖if p ∈ tsupport (d.B.weight a.1) then
        d.B.phaseCovectorRead i (d.globalPhases a) (chart (i : M) p) else 0‖ ≤ D
      split_ifs with ha
      · have he := d.B.covectorFrame_mfderiv (d.globalPhases a)
          (d.B.curvedAtlasPhase_smooth d.localPhases (fun _ _ => PhaseGeometry.centeredConvexPhase_smooth _ _ _) a) i hs
        unfold SmoothingAtlas.phaseCovectorRead
        rw [← he]
        exact (hv a i p hp).trans (hvD a)
      · simpa only [norm_zero] using hn
  · change ‖(d.B.tensorTriv i).continuousLinearMapAt ℝ
      ((chart (i : M)).symm (chart (i : M) p))
      (gref.inner ((chart (i : M)).symm (chart (i : M) p)))‖ ≤ D
    rw [(chart (i : M)).left_inv hs,d.B.tensor_frame_read i gref.inner gref.symm hp]
    exact (hH i (chart (i : M) p) ⟨p,hp,rfl⟩).trans (hHD i)

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
