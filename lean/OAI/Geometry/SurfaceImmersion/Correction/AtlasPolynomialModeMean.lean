import OAI.Geometry.SurfaceImmersion.Correction.AtlasCombinedModes
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialQuadrature
import OAI.Geometry.SurfaceImmersion.Correction.AtlasSupportedPolynomialQuadratic
import OAI.Geometry.SurfaceImmersion.Correction.AtlasMetricLocalModel

namespace OAI

/-! The full quadratic global interaction has one supported family of
oscillatory targets, including the polynomial perturbation. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance modeMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance modeMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance modeMeanDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance modeMeanDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance modeMeanSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance modeMeanSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)



def polynomialModeMean {m : ℕ}
    (Q : A.centers → Fin 3 → Fin m → Expression) (F : M → Space) (ε τ : ℝ)
    (φ : M → ℝ) (Z : M → Fin 4 → ℂ) : ∀ p : M, CovariantTwoTensor p :=
  A.tensorPlaneRestore (fun i y => (A.planeWeight i y)^2 •
    (fun k => quadraticMeanCoefficient (Q i k) ε (A.jetChartMap i F)
      (A.vectorChartRead i φ) (A.vectorChartRead i Z) τ 0 (planeCoordinateIsometry.symm y)))

lemma local_single_mode_quadratic {m : ℕ} (i : A.centers)
    (Q : Fin 3 → Fin m → Expression) (ε : ℝ) (G : Base → JetPolynomial.Space)
    (τ : ℝ) (φ : M → ℝ) (Z : M → Fin 4 → ℂ)
    {x : Base} (hx : A.chartWeight i x ≠ 0) :
    coordinateQuadraticPolynomial Q ε G
      (A.jetChartMap i (spaceCoordinates.symm ∘ surfaceMode τ φ Z) ∘ planeCoordinateIsometry.symm)
      0 (planeCoordinateIsometry x) =
    coordinateQuadraticPolynomial Q ε G
      (QuadraticMean.displacement τ (A.vectorPlaneRead i φ) (A.vectorPlaneRead i Z))
      0 (planeCoordinateIsometry x) := by
  have hh := A.jetChartMap_modes_germ (ι := Unit) i τ (fun _ => φ) (fun _ => Z) hx
  have he : (A.jetChartMap i (spaceCoordinates.symm ∘ surfaceMode τ φ Z) ∘
      planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry =ᶠ[𝓝 x]
      QuadraticMean.displacement τ (A.vectorPlaneRead i φ) (A.vectorPlaneRead i Z) ∘
        planeCoordinateIsometry := by
    simpa only [Fintype.sum_unique,QuadraticMean.sumDisplacement,vectorPlaneRead,
      Function.comp_def,planeCoordinateIsometry.symm_apply_apply] using hh
  exact coordinateQuadraticPolynomial_eq_of_eventuallyEq Q ε G he 0

theorem polynomial_mode_quadrature {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hrep : A.PolynomialQuadraticRepresentation P Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
    (φ : M → ℝ) (Z : M → Fin 4 → ℂ)
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ Z) :
    A.atlasPolynomialQuadratic P ε F (spaceCoordinates.symm ∘ surfaceMode τ φ Z)+
      A.atlasPolynomialQuadratic P ε F
        (spaceCoordinates.symm ∘ surfaceMode τ φ (fun p => Complex.I • Z p)) =
      (2 : ℝ) • A.polynomialModeMean Q F ε τ φ Z := by
  let W := spaceCoordinates.symm ∘ surfaceMode τ φ Z
  let WI := spaceCoordinates.symm ∘ surfaceMode τ φ (fun p => Complex.I • Z p)
  have hi : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (fun p => Complex.I • Z p) :=
    ((contDiff_const (c := Complex.I)).smul contDiff_id).contMDiff.comp hZ
  have hW : ContMDiff planeModel spaceModel ∞ W :=
    spaceCoordinates.symm.contDiff.contMDiff.comp (surfaceMode_smooth τ hφ hZ)
  have hWI : ContMDiff planeModel spaceModel ∞ WI :=
    spaceCoordinates.symm.contDiff.contMDiff.comp (surfaceMode_smooth τ hφ hi)
  let R := A.atlasPolynomialQuadratic P ε F W+A.atlasPolynomialQuadratic P ε F WI
  have hs : ∀ p v w, R p v w = R p w v := by
    intro p v w
    exact congrArg₂ (· + ·) (A.tensorPlaneRestore_symmetric _ p v w)
      (A.tensorPlaneRestore_symmetric _ p v w)
  change R = _
  rw [← A.tensorPlaneRestore_encode R hs]
  unfold polynomialModeMean
  rw [← A.tensorPlaneRestore_smul]
  congr 1
  funext i y
  rw [A.tensorPlaneEncode_weight]
  by_cases hz : A.planeWeight i y = 0
  · simp only [hz,zero_pow (by decide : 2 ≠ 0),zero_smul,Pi.smul_apply,smul_zero]
  · have hx : A.chartWeight i (planeCoordinateIsometry.symm y) ≠ 0 := hz
    have hc : planeCoordinateIsometry.symm y ∈ (A.chartWeightCompact i : Set Base) := by
      rw [← A.chartWeight_tsupport i]
      exact subset_tsupport _ hx
    have hr := hrep F W hF hW i _ hc ε
    have hri := hrep F WI hF hWI i _ hc ε
    have he := A.local_single_mode_quadratic i (Q i) ε (A.jetChartMap i F) τ φ Z hx
    have hei := A.local_single_mode_quadratic i (Q i) ε (A.jetChartMap i F) τ φ
      (fun p => Complex.I • Z p) hx
    simp only [planeCoordinateIsometry.apply_symm_apply] at hr hri he hei
    change (A.planeWeight i y)^2 • A.tensorChartRead i R (planeCoordinateIsometry.symm y) = _
    dsimp only [R]
    rw [A.tensorChartRead_add]
    simp only [Pi.add_apply]
    rw [← hr,← hri,he,hei]
    have hreadI : A.vectorPlaneRead i (fun p => Complex.I • Z p) =
        coordinateAmplitude (fun x => Complex.I • A.vectorChartRead i Z x) := by
      rw [A.vectorPlaneRead_const_smul]
      rfl
    rw [hreadI]
    have hq := congrFun (coordinate_polynomial_quadrature (Q i) ε (A.jetChartMap i F)
      (A.vectorChartRead_smooth i hφ) (A.vectorChartRead_smooth i hZ) τ 0) y
    simp only [Pi.add_apply,Pi.smul_apply] at hq ⊢
    rw [show A.vectorPlaneRead i φ = coordinatePhase (A.vectorChartRead i φ) from rfl,
      show A.vectorPlaneRead i Z = coordinateAmplitude (A.vectorChartRead i Z) from rfl,hq]
    exact smul_comm _ _ _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
