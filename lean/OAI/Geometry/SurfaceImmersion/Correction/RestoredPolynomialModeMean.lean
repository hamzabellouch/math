import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialModeMean
import OAI.Geometry.SurfaceImmersion.Correction.RestoredQuadratureMean

namespace OAI

/-! The full quadratic global interaction has one supported family of
oscillatory targets, including the polynomial perturbation. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance restoredPolynomialMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance restoredPolynomialMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance restoredPolynomialMeanDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance restoredPolynomialMeanDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance restoredPolynomialMeanSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance restoredPolynomialMeanSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)




lemma real_restored_polynomial_quadratic {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hrep : A.PolynomialQuadraticRepresentation P Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε : ℝ)
    (i : A.centers) (X : RealModes.RField 4) (hX : ContDiff ℝ ∞ X)
    (hsp : tsupport X ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.atlasPolynomialQuadratic P ε F
      (spaceCoordinates.symm ∘ restore (i : M) (A.outer i) (X ∘ planeCoordinateIsometry)) =
      A.bundleRestore A.tensorTriv i (fun x => fiberFromThree
        (coordinateQuadraticPolynomial (Q i) ε (A.jetChartMap i F) X 0
          (planeCoordinateIsometry x))) := by
  let W := restore (i : M) (A.outer i)
    ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)
  have hW : ContMDiff planeModel spaceModel ∞ W := restore_smooth (i : M)
    (A.outer_smooth i) (A.outer_support i)
    ((spaceCoordinates.symm.contDiff.comp hX).comp planeCoordinateIsometry.contDiff)
  have he : W = spaceCoordinates.symm ∘
      restore (i : M) (A.outer i) (X ∘ planeCoordinateIsometry) := by
    funext p
    by_cases hp : p ∈ (chart (i : M)).source <;>
      simp [W,restore,hp,Function.comp_apply,map_smul]
  have hj : A.jetChartMap i W ∘ planeCoordinateIsometry.symm = X := by
    rw [A.jetChartMap_restored_direction i X hsp]
    funext x
    simp only [Function.comp_apply,planeCoordinateIsometry.apply_symm_apply]
  rw [← he]
  apply A.restored_polynomial_quadratic P i (Q i) F X hsp ε
  intro x hx
  have hr := hrep F W hF hW i x hx ε
  simpa only [hj] using hr

theorem restored_polynomial_mode_mean {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hrep : A.PolynomialQuadraticRepresentation P Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
    (i : A.centers) (φ : SmallModes.Base → ℝ) (Z : SmallModes.Base → Fin 4 → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z)
    (hs : tsupport Z ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    let Φ := restore (i : M) (A.outer i) (φ ∘ planeCoordinateIsometry)
    let W := restore (i : M) (A.outer i) (Z ∘ planeCoordinateIsometry)
    A.polynomialModeMean Q F ε τ Φ W =
      A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
        (fun k => quadraticMeanCoefficient (Q i k) ε (A.jetChartMap i F)
          (φ ∘ planeCoordinateIsometry) (Z ∘ planeCoordinateIsometry) τ 0 y)) := by
  dsimp only
  let Φ := restore (i : M) (A.outer i) (φ ∘ planeCoordinateIsometry)
  let W := restore (i : M) (A.outer i) (Z ∘ planeCoordinateIsometry)
  let ZI := fun x => Complex.I • Z x
  have hΦ : ContMDiff planeModel 𝓘(ℝ) ∞ Φ := restore_smooth (i : M)
    (A.outer_smooth i) (A.outer_support i) (hφ.comp planeCoordinateIsometry.contDiff)
  have hW : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ W := restore_smooth (i : M)
    (A.outer_smooth i) (A.outer_support i) (hZ.comp planeCoordinateIsometry.contDiff)
  have hZI : ContDiff ℝ ∞ ZI := (contDiff_const (c := Complex.I)).smul hZ
  have hsI : tsupport ZI ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
    (tsupport_smul_subset_right (fun _ => Complex.I) Z).trans hs
  have hWI : (fun p => Complex.I • W p) =
      restore (i : M) (A.outer i) (ZI ∘ planeCoordinateIsometry) := by
    funext p
    by_cases hp : p ∈ (chart (i : M)).source
    · simp only [W,ZI,restore,indicator_of_mem hp,Function.comp_apply]
      exact smul_comm _ _ _
    · simp only [W,restore,indicator_of_notMem hp,smul_zero]
  have hdisp := contDiffOn_univ.mp (RealModes.contDiffOn_displacement hφ.contDiffOn hZ.contDiffOn τ)
  have hdispI := contDiffOn_univ.mp (RealModes.contDiffOn_displacement hφ.contDiffOn hZI.contDiffOn τ)
  have hsdisp := (surfaceMode_tsupport τ φ Z).trans hs
  have hsdispI := (surfaceMode_tsupport τ φ ZI).trans hsI
  have he := A.polynomial_mode_quadrature P Q hrep F hF ε τ Φ W hΦ hW
  rw [hWI,← A.restore_displacement i τ φ Z hs,← A.restore_displacement i τ φ ZI hsI,
    A.real_restored_polynomial_quadratic P Q hrep F hF ε i _ hdisp hsdisp,
    A.real_restored_polynomial_quadratic P Q hrep F hF ε i _ hdispI hsdispI] at he
  have hc :
      (fun y => fiberFromThree (coordinateQuadraticPolynomial (Q i) ε (A.jetChartMap i F)
        (QuadraticMean.displacement τ φ Z) 0 (planeCoordinateIsometry y)))+
      (fun y => fiberFromThree (coordinateQuadraticPolynomial (Q i) ε (A.jetChartMap i F)
        (QuadraticMean.displacement τ φ ZI) 0 (planeCoordinateIsometry y))) =
      (2 : ℝ) • (fun y => fiberFromThree (fun k =>
        quadraticMeanCoefficient (Q i k) ε (A.jetChartMap i F)
          (φ ∘ planeCoordinateIsometry) (Z ∘ planeCoordinateIsometry) τ 0 y)) := by
    have hq := coordinate_polynomial_quadrature (Q i) ε (A.jetChartMap i F)
      (hφ.comp planeCoordinateIsometry.contDiff) (hZ.comp planeCoordinateIsometry.contDiff) τ 0
    have hφback : coordinatePhase (φ ∘ planeCoordinateIsometry) = φ := by
      funext x
      simp only [coordinatePhase,Function.comp_apply,planeCoordinateIsometry.apply_symm_apply]
    have hZback : coordinateAmplitude (Z ∘ planeCoordinateIsometry) = Z := by
      funext x
      simp only [coordinateAmplitude,Function.comp_apply,planeCoordinateIsometry.apply_symm_apply]
    have hZIback : coordinateAmplitude (fun p => Complex.I • (Z ∘ planeCoordinateIsometry) p) = ZI := by
      funext x
      simp only [coordinateAmplitude,Function.comp_apply,planeCoordinateIsometry.apply_symm_apply,ZI]
    rw [hφback,hZback,hZIback] at hq
    funext y
    change fiberFromThree _ + fiberFromThree _ = (2 : ℝ) • fiberFromThree _
    rw [← map_add]
    have hh := congrFun hq (planeCoordinateIsometry y)
    simp only [Pi.add_apply,Pi.smul_apply,planeCoordinateIsometry.symm_apply_apply] at hh
    rw [hh,map_smul]
  rw [← A.bundleRestore_add,hc,A.bundleRestore_smul] at he
  have hh := congrArg (fun X => (1/2 : ℝ) • X) he
  simpa only [smul_smul,show (1/2 : ℝ)*2 = 1 by norm_num,one_smul] using hh.symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
