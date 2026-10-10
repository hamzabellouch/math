import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialLocalModel

namespace OAI

/-! Local coordinate models of the complete perturbed global metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance metricLocalFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance metricLocalFiberAdd : AddCommGroup TensorFiber :=
  metricLocalFiberNormed.toAddCommGroup
local instance metricLocalFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance metricLocalDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricLocalDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricLocalSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricLocalSectionAdd (p : M) : AddCommGroup (CovariantTwoTensor p) :=
  (metricLocalSectionNormed p).toAddCommGroup
local instance metricLocalSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma tensorChartRead_add (i : A.centers) (u v : ∀ p : M, CovariantTwoTensor p) :
    A.tensorChartRead i (u+v) = A.tensorChartRead i u+A.tensorChartRead i v := by
  have h := A.tensorChartRead_sum i ![u,v]
  simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using h

lemma metric_read_on_support (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {x : Base}
    (hx : x ∈ (A.chartWeightCompact i : Set Base)) :
    RealModes.realMetricTensor (A.jetChartMap i F ∘ planeCoordinateIsometry.symm)
        (planeCoordinateIsometry x) = A.tensorChartRead i (inducedTensor F) x := by
  obtain ⟨p,hp,rfl⟩ := hx
  have hread := A.tensorChartRead_on_weight i (inducedTensor F) hp
  rw [A.metric_component_on_weight i hF hp,fiberToThree_fromThree] at hread
  exact hread.symm

theorem atlas_metric_local_model {n : A.centers → ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) (i : A.centers) :
    ∃ Q : Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
      (∀ k r, (Q k r).SmoothCoeffs univ) ∧
      ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
        ∀ x ∈ (A.chartWeightCompact i : Set Base), ∀ ε : ℝ,
          coordinateMetricMap Q ε (A.jetChartMap i F) (planeCoordinateIsometry x) =
            A.tensorChartRead i (A.atlasPolynomialMetric P ε F) x := by
  obtain ⟨Q,hQ,hvalue⟩ := A.atlas_polynomial_representation_on_support P hP i
  refine ⟨Q,hQ,?_⟩
  intro F hF x hx ε
  simp only [coordinateMetricMap,Pi.add_apply,atlasPolynomialMetric,A.tensorChartRead_add,
    A.metric_read_on_support i hF hx,hvalue F hF x hx ε]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
