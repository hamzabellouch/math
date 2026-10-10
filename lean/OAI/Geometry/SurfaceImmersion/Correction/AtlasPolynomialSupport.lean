import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialCalculus
import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialLocality

namespace OAI

/-! The global polynomial variation is local in its varying field.
In particular, restoring the polynomial does not enlarge that support. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance polynomialSupportFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialSupportFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance polynomialSupportDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialSupportDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialSupportSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialSupportSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma jetChartMap_eventually_zero (i : A.centers) {X : M → Space} {p : M}
    (hp : p ∈ (chart (i : M)).source) (hX : X =ᶠ[𝓝 p] 0) :
    A.jetChartMap i X =ᶠ[𝓝 (chart (i : M) p)] 0 := by
  have ht := (chart (i : M)).map_source hp
  have hc : Tendsto (chart (i : M)).symm (𝓝 (chart (i : M) p)) (𝓝 p) := by
    simpa only [(chart (i : M)).left_inv hp] using
      ((chart (i : M)).continuousAt_symm ht).tendsto
  have he := hX.comp_tendsto hc
  filter_upwards [he,(chart (i : M)).open_target.mem_nhds ht] with y hy hyt
  change X ((chart (i : M)).symm y) = 0 at hy
  change spaceCoordinates (localize (i : M) (A.outer i) X y) = 0
  simp only [localize,indicator_of_mem hyt,hy,smul_zero,map_zero]

lemma atlasPolynomialVariation_zero_of_notMem {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression) (ε : ℝ)
    (F X : M → Space) {p : M} (hp : p ∉ tsupport X) :
    A.atlasPolynomialVariation P ε F X p = 0 := by
  classical
  unfold atlasPolynomialVariation tensorPlaneRestore
  apply Finset.sum_eq_zero
  intro i _
  by_cases ho : A.outer i p = 0
  · simp only [bundleRestore,ho,zero_smul]
  · have hps := A.outer_support i (subset_tsupport (A.outer i) ho)
    have hz := A.jetChartMap_eventually_zero i hps (notMem_tsupport_iff_eventuallyEq.mp hp)
    have hn : chart (i : M) p ∉ tsupport (A.jetChartMap i X) :=
      notMem_tsupport_iff_eventuallyEq.mpr hz
    have hcomp : (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) ∘
        planeCoordinateIsometry = A.jetChartMap i X := by
      funext y
      simp only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
    have he : coordinateRealLinearized (P i) ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0
        (planeCoordinateIsometry (chart (i : M) p)) = 0 := by
      funext k
      simp only [coordinateRealLinearized,linearized,hcomp,
        planeCoordinateIsometry.symm_apply_apply,Pi.zero_apply]
      apply Finset.sum_eq_zero
      intro l _
      rw [(P i k l).variation_zero_of_notMem (A.jetChartMap i F) hn 0,mul_zero]
    simp only [bundleRestore,he,map_zero,smul_zero]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
