import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialLocalModel
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialSupport

namespace OAI

/-! The variation of a globally defined polynomial in a chart-supported
direction is the restoration of that chart's actual local linearization. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance supportedVariationFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance supportedVariationFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance supportedVariationDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance supportedVariationDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance supportedVariationSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance supportedVariationSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma restore_chart_read_on_weight (i : A.centers) (u : ∀ p : M, CovariantTwoTensor p)
    {p : M} (hp : p ∈ tsupport (A.weight i)) (hu : ∀ v w, u p v w = u p w v) :
    A.bundleRestore A.tensorTriv i (fun x => fiberFromThree (A.tensorChartRead i u x)) p = u p := by
  have hsource := A.weight_support i hp
  have hc : ∀ v w, A.bundleComponent A.tensorTriv i u p v w =
      A.bundleComponent A.tensorTriv i u p w v := by
    intro v w
    rw [A.tensorComponent_apply i u hsource,A.tensorComponent_apply i u hsource]
    exact hu _ _
  change A.outer i p • (A.tensorTriv i).symmL ℝ p
    (fiberFromThree (A.tensorChartRead i u (chart (i : M) p))) = _
  rw [A.tensorChartRead_on_weight i u hp,fiberFromThree_toThree _ hc,
    A.outer_one i p hp,one_smul]
  exact (A.tensorTriv i).symmL_continuousLinearMapAt (A.tensorTriv_domain i hsource) _

theorem supported_polynomial_variation {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (i : A.centers) (Q : Fin 3 → Fin m → Expression)
    (F X : M → Space)
    (hsp : tsupport X ⊆ tsupport (A.weight i)) (ε : ℝ)
    (hread : ∀ x ∈ (A.chartWeightCompact i : Set Base),
      coordinateRealLinearized Q ε (A.jetChartMap i F)
          (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x) =
        A.tensorChartRead i (A.atlasPolynomialVariation P ε F X) x) :
    A.atlasPolynomialVariation P ε F X = A.bundleRestore A.tensorTriv i
      (fun x => fiberFromThree (coordinateRealLinearized Q ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x))) := by
  funext p
  by_cases hp : p ∈ tsupport (A.weight i)
  · have he := A.restore_chart_read_on_weight i (A.atlasPolynomialVariation P ε F X) hp
      (A.tensorPlaneRestore_symmetric _ p)
    have hr := hread (chart (i : M) p) ⟨p,hp,rfl⟩
    change _ = A.outer i p • (A.tensorTriv i).symmL ℝ p (fiberFromThree _)
    rw [hr]
    exact he.symm
  · have hX : p ∉ tsupport X := fun hx => hp (hsp hx)
    rw [A.atlasPolynomialVariation_zero_of_notMem P ε F X hX]
    by_cases ho : A.outer i p = 0
    · simp only [bundleRestore,ho,zero_smul]
    · have hsource := A.outer_support i (subset_tsupport (A.outer i) ho)
      have hn : chart (i : M) p ∉ tsupport (A.jetChartMap i X) :=
        notMem_tsupport_iff_eventuallyEq.mpr
          (A.jetChartMap_eventually_zero i hsource (notMem_tsupport_iff_eventuallyEq.mp hX))
      have hcomp : (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) ∘
          planeCoordinateIsometry = A.jetChartMap i X := by
        funext y
        simp only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
      have hz : coordinateRealLinearized Q ε (A.jetChartMap i F)
          (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0
          (planeCoordinateIsometry (chart (i : M) p)) = 0 := by
        funext k
        simp only [coordinateRealLinearized,linearized,hcomp,
          planeCoordinateIsometry.symm_apply_apply,Pi.zero_apply]
        apply Finset.sum_eq_zero
        intro l _
        rw [(Q k l).variation_zero_of_notMem (A.jetChartMap i F) hn 0,mul_zero]
      simp only [bundleRestore,hz,map_zero,smul_zero]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
