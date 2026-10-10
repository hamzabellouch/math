import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialRestoredRead

namespace OAI

/-! Global coefficient extensions for one restored polynomial tensor.
The representation holds on the open nonzero partition-weight locus,
including chart points outside the support of the restored term. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
local instance restoredPolyFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance restoredPolyFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance restoredPolyDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance restoredPolyDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance restoredPolySectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance restoredPolySectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma tensorChartRead_restore_zero (i j : A.centers) (f : Base → TensorFiber)
    {x : Base} (hx : x ∈ (chart (i : M)).target)
    (hz : A.outer j ((chart (i : M)).symm x) = 0) :
    A.tensorChartRead i (A.bundleRestore A.tensorTriv j f) x = 0 := by
  simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
    indicator_of_mem hx,bundleComponent,bundleRestore,hz,zero_smul,map_zero,smul_zero]

theorem restored_polynomial_representation (i j : A.centers) {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k r, (P k r).SmoothCoeffs univ) :
    ∃ P' : Fin 3 → Fin n → Expression, (∀ k r, (P' k r).SmoothCoeffs univ) ∧
      ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
        ∀ (x : Base), A.chartWeight i x ≠ 0 → ∀ ε t : ℝ,
          coordinatePolynomialValue P' ε (A.jetChartMap i F) t (JetPolynomial.planeCoordinateIsometry x) =
            A.tensorChartRead i (A.bundleRestore A.tensorTriv j
              (fun y => fiberFromThree (coordinatePolynomialValue P ε
                (A.jetChartMap j F) t (JetPolynomial.planeCoordinateIsometry y)))) x := by
  obtain ⟨U,hU,hKU,hUe,Q,hQ,hread⟩ := A.compact_restored_polynomial_read i j P hP
    (A.pairSupport_compact i j) (A.pairSupport_transition i j)
  obtain ⟨χ,hχ,_,_,hχU,hχone⟩ :=
    CollarVelocity.compact_cutoff (A.pairSupport_compact i j) hU hKU
  let L : Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor :=
    fun x => χ x • ContinuousLinearMap.id ℝ PhaseMean.Tensor
  have hL : ContDiff ℝ ∞ L := hχ.smul contDiff_const
  refine ⟨mapTensorPolynomial L Q,mapTensorPolynomial_smooth hL hQ,?_⟩
  intro F hF x hx ε t
  have hxt : x ∈ (chart (i : M)).target := by
    by_contra hn
    exact hx (by simp only [chartWeight,indicator_of_notMem hn])
  have hw : A.weight i ((chart (i : M)).symm x) ≠ 0 := by
    simpa only [chartWeight,indicator_of_mem hxt] using hx
  have hvalue := mapTensorPolynomial_eval L Q ε (A.jetChartMap i F) t x
  rw [hvalue]
  change χ x • coordinatePolynomialValue Q ε (A.jetChartMap i F) t
    (JetPolynomial.planeCoordinateIsometry x) = _
  by_cases hz : A.outer j ((chart (i : M)).symm x) = 0
  · have hzero := A.tensorChartRead_restore_zero i j
      (fun y => fiberFromThree (coordinatePolynomialValue P ε (A.jetChartMap j F) t
        (JetPolynomial.planeCoordinateIsometry y))) hxt hz
    by_cases hxU : x ∈ U
    · rw [hread F hF x hxU hw ε t,hzero,smul_zero]
    · have hχx : χ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxU (hχU h))
      rw [hχx,zero_smul,hzero]
  · have hxK : x ∈ A.pairSupport i j := by
      refine ⟨(chart (i : M)).symm x,⟨subset_tsupport _ hw,subset_tsupport _ hz⟩,?_⟩
      exact (chart (i : M)).right_inv hxt
    rw [hχone x hxK,one_smul,hread F hF x (hKU hxK) hw ε t]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
