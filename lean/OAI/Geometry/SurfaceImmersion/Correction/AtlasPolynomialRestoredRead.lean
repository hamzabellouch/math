import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialCoordinateRead
import OAI.Geometry.SurfaceImmersion.Geometry.TensorExpressionLinearMap
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasTensorTransition

namespace OAI

/-! A restored polynomial tensor has a constructed finite jet expression
in every overlapping correction chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
local instance restoredReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance restoredReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance restoredReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance restoredReadDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance restoredReadSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance restoredReadSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem compact_restored_polynomial_read (i j : A.centers) {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k r, (P k r).SmoothCoeffs univ)
    {K : Set Base} (hK : IsCompact K)
    (hKe : K ⊆ (transition (i : M) (j : M)).source) :
    ∃ U : Set Base, IsOpen U ∧ K ⊆ U ∧
      U ⊆ (transition (i : M) (j : M)).source ∧
      ∃ P' : Fin 3 → Fin n → Expression, (∀ k r, (P' k r).SmoothCoeffs univ) ∧
        ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
          ∀ (x : Base), x ∈ U → A.weight i ((chart (i : M)).symm x) ≠ 0 →
            ∀ ε t : ℝ,
              coordinatePolynomialValue P' ε (A.jetChartMap i F) t
                  (JetPolynomial.planeCoordinateIsometry x) =
                A.tensorChartRead i (A.bundleRestore A.tensorTriv j
                  (fun y => fiberFromThree (coordinatePolynomialValue P ε
                    (A.jetChartMap j F) t (JetPolynomial.planeCoordinateIsometry y)))) x := by
  obtain ⟨U₁,hU₁,hKU₁,hU₁e,Q,hQ,hvalue⟩ :=
    A.compact_polynomial_coordinate_read i j P hP hK hKe
  obtain ⟨U₂,hU₂,hKU₂,hU₂e,L,hL,hLe,_⟩ :=
    A.compact_tensorRestoreTransition i j hK hKe
  refine ⟨U₁ ∩ U₂,hU₁.inter hU₂,fun x hx => ⟨hKU₁ hx,hKU₂ hx⟩,
    fun x hx => hU₁e hx.1,mapTensorPolynomial L Q,
    mapTensorPolynomial_smooth hL hQ,?_⟩
  intro F hF x hx hw ε t
  have hq := hvalue F hF x hx.1 hw ε t
  have hr := A.tensorChartRead_restoreThree i j
    (fun y => coordinatePolynomialValue P ε (A.jetChartMap j F) t
      (JetPolynomial.planeCoordinateIsometry y)) (hU₁e hx.1)
    (A.outer_one i _ (subset_tsupport (A.weight i) hw))
  calc
    _ = L x (coordinatePolynomialValue Q ε (A.jetChartMap i F) t
        (JetPolynomial.planeCoordinateIsometry x)) :=
      mapTensorPolynomial_eval L Q ε (A.jetChartMap i F) t x
    _ = L x (coordinatePolynomialValue P ε (A.jetChartMap j F) t
        (JetPolynomial.planeCoordinateIsometry (transition (i : M) (j : M) x))) :=
      congrArg (L x) hq
    _ = A.tensorRestoreTransition i j x
        (coordinatePolynomialValue P ε (A.jetChartMap j F) t
          (JetPolynomial.planeCoordinateIsometry (transition (i : M) (j : M) x))) :=
      congrArg (fun C : PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor => C
        (coordinatePolynomialValue P ε (A.jetChartMap j F) t
          (JetPolynomial.planeCoordinateIsometry (transition (i : M) (j : M) x)))) (hLe hx.2)
    _ = _ := hr.symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
