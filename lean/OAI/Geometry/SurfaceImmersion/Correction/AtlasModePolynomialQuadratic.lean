import OAI.Geometry.SurfaceImmersion.Correction.AtlasModeQuadraticExpansion
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialLocalModel

namespace OAI

/-! The polynomial part of the quadratic global mode interaction splits
into its zero-phase mean and all nonzero quadratic phases. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance modePolynomialFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance modePolynomialFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance modePolynomialDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance modePolynomialDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance modePolynomialSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance modePolynomialSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem atlas_mode_polynomial_quadratic {n : A.centers → ℕ} {m : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hrep : A.PolynomialQuadraticRepresentation P Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j)) :
    A.atlasPolynomialQuadratic P ε F
        (spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)) =
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        coordinateQuadraticMean (Q i) ε (A.jetChartMap i F)
          (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j)) τ 0 x)+
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        ∑ l : RealModes.QuadraticLabel ι,
          QuadraticMean.displacement τ
            (RealModes.quadraticPhase (fun j => coordinatePhase (A.vectorChartRead i (φ j))) l)
            (coordinateQuadraticCoefficient (Q i) ε (A.jetChartMap i F)
              (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j)) τ 0 l) x) := by
  let W : M → Space := spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)
  have hsum : ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞
      (∑ j, surfaceMode τ (φ j) (Z j)) := by
    convert ContMDiff.sum (t := Finset.univ) (fun j _ => surfaceMode_smooth τ (hφ j) (hZ j)) using 1
    funext p
    simp only [Finset.sum_apply]
  have hW : ContMDiff planeModel spaceModel ∞ W :=
    spaceCoordinates.symm.contDiff.contMDiff.comp hsum
  have hsym : ∀ p v w, A.atlasPolynomialQuadratic P ε F W p v w =
      A.atlasPolynomialQuadratic P ε F W p w v := A.tensorPlaneRestore_symmetric _
  change A.atlasPolynomialQuadratic P ε F W = _
  rw [← A.tensorPlaneRestore_encode (A.atlasPolynomialQuadratic P ε F W) hsym,
    ← A.tensorPlaneRestore_add]
  congr 1
  funext i y
  rw [A.tensorPlaneEncode_weight]
  by_cases hz : A.planeWeight i y = 0
  · simp only [hz,zero_pow (by decide : 2 ≠ 0),zero_smul,Pi.add_apply,zero_add]
  · have hx : A.chartWeight i (planeCoordinateIsometry.symm y) ≠ 0 := hz
    have hs : planeCoordinateIsometry.symm y ∈ (A.chartWeightCompact i : Set Base) := by
      rw [← A.chartWeight_tsupport i]
      exact subset_tsupport (A.chartWeight i) hx
    have hr := hrep F W hF hW i (planeCoordinateIsometry.symm y) hs ε
    simp only [planeCoordinateIsometry.apply_symm_apply] at hr
    have he := A.local_mode_polynomial_quadratic i (Q i) ε (A.jetChartMap i F)
      τ φ Z hφ hZ hx
    simp only [planeCoordinateIsometry.apply_symm_apply] at he
    change (A.planeWeight i y)^2 • A.tensorChartRead i (A.atlasPolynomialQuadratic P ε F W)
      (planeCoordinateIsometry.symm y) = _
    rw [← hr,he,smul_add]
    rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
