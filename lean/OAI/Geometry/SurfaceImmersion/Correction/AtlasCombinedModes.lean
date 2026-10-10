import OAI.Geometry.SurfaceImmersion.Correction.AtlasModePolynomialQuadratic
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasQuadraticTargets
import OAI.Geometry.SurfaceImmersion.Geometry.CombinedQuadraticExpansion
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialQuadraticTargets

namespace OAI

/-! The full quadratic global interaction has one supported family of
oscillatory targets, including the polynomial perturbation. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
local instance combinedModesFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance combinedModesFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance combinedModesDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance combinedModesDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance combinedModesSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance combinedModesSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)


variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def globalPolynomialQuadraticMean {m : ℕ}
    (Q : A.centers → Fin 3 → Fin m → Expression) (F : M → Space) (ε τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ) : ∀ p : M, CovariantTwoTensor p :=
  A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
    combinedQuadraticMean (Q i) ε (A.jetChartMap i F)
      (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j)) τ 0 x)

def globalPolynomialQuadraticTarget {m : ℕ}
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j))
    (i : A.centers) (l : RealModes.QuadraticLabel ι) :
    SupportedField (F := ComplexTensor) (modeSupport (A.chartWeightCompact i)) where
  toFun := fun x => (A.planeWeight i x)^2 •
    combinedQuadraticCoefficient (Q i) ε (A.jetChartMap i F)
      (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j)) τ 0 l x
  contDiff' := by
    apply ((A.planeWeight_smooth i).pow 2).smul
    apply ContDiff.add
    · exact RealModes.quadraticAmplitude_smooth
        (fun j => A.vectorPlaneRead_smooth i (hφ j))
        (fun j => A.vectorPlaneRead_smooth i (hZ j)) τ l
    · apply contDiff_pi.mpr
      intro k
      exact (contDiffOn_univ.mp (quadraticFamilyCoefficient_smooth isOpen_univ (hQ i k)
        (A.jetChartMap_smooth i hF) (fun j => A.vectorChartRead_smooth i (hφ j))
        (fun j => A.vectorChartRead_smooth i (hZ j)) (fun _ _ => mem_univ _) ε τ 0 l)).comp
          planeCoordinateIsometry.symm.contDiff
  zero_on_compl' := by
    intro x hx
    have hw := (A.supportedPlaneWeight i).zero_on_compl hx
    change A.planeWeight i x = 0 at hw
    simp only [hw,zero_pow (by decide : 2 ≠ 0),zero_smul,Pi.zero_apply]

theorem globalPolynomialQuadraticTarget_expansion {m : ℕ}
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j)) :
    A.tensorPlaneRestore (fun i x => ∑ l : RealModes.QuadraticLabel ι,
      QuadraticMean.displacement τ (coordinatePhase (A.globalQuadraticPhase φ i l))
        (A.globalPolynomialQuadraticTarget Q hQ F hF ε τ φ Z hφ hZ i l) x) =
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        (RealModes.nonzeroPhaseSum τ (fun j => A.vectorPlaneRead i (φ j))
          (fun j => A.vectorPlaneRead i (Z j)) x +
         ∑ l : RealModes.QuadraticLabel ι,
          QuadraticMean.displacement τ
            (RealModes.quadraticPhase (fun j => coordinatePhase (A.vectorChartRead i (φ j))) l)
            (coordinateQuadraticCoefficient (Q i) ε (A.jetChartMap i F)
              (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j)) τ 0 l) x)) := by
  congr 1
  funext i x
  rw [RealModes.nonzeroPhaseSum_eq_quadraticFamily,← Finset.sum_add_distrib,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have hp : coordinatePhase (A.globalQuadraticPhase φ i l) =
      RealModes.quadraticPhase (fun j => A.vectorPlaneRead i (φ j)) l := by
    funext y
    simp only [coordinatePhase,globalQuadraticPhase,Function.comp_apply,
      planeCoordinateIsometry.apply_symm_apply]
  rw [hp]
  change QuadraticMean.realMode _ ((A.planeWeight i x)^2 • (_ + _)) = _
  rw [realMode_smul]
  change (A.planeWeight i x)^2 • QuadraticMean.displacement τ _
    (combinedQuadraticCoefficient (Q i) ε (A.jetChartMap i F)
      (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j)) τ 0 l) x = _
  rw [combinedQuadraticCoefficient,displacement_add]
  rfl

theorem global_modes_full_quadratic {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ)
    (hrep : A.PolynomialQuadraticRepresentation P Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j)) :
    let W := spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)
    inducedTensor W + A.atlasPolynomialQuadratic P ε F W =
      A.globalPolynomialQuadraticMean Q F ε τ φ Z +
      A.tensorPlaneRestore (fun i x => ∑ l : RealModes.QuadraticLabel ι,
        QuadraticMean.displacement τ (coordinatePhase (A.globalQuadraticPhase φ i l))
          (A.globalPolynomialQuadraticTarget Q hQ F hF ε τ φ Z hφ hZ i l) x) := by
  dsimp only
  rw [A.global_modes_metric τ φ Z hφ hZ,
    A.atlas_mode_polynomial_quadratic P Q hrep F hF ε τ φ Z hφ hZ,
    A.globalPolynomialQuadraticTarget_expansion Q hQ F hF ε τ φ Z hφ hZ]
  have hm : A.globalPolynomialQuadraticMean Q F ε τ φ Z =
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        RealModes.zeroPhaseSum τ (fun j => A.vectorPlaneRead i (φ j))
          (fun j => A.vectorPlaneRead i (Z j)) x) +
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        coordinateQuadraticMean (Q i) ε (A.jetChartMap i F)
          (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j)) τ 0 x) := by
    rw [← A.tensorPlaneRestore_add]
    unfold globalPolynomialQuadraticMean
    congr 1
    funext i x
    exact smul_add _ _ _
  rw [hm]
  have ha (f g : A.centers → SmallModes.Base → Tensor) :
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 • (f i x + g i x)) =
        A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 • f i x) +
        A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 • g i x) := by
    rw [← A.tensorPlaneRestore_add]
    congr 1
    funext i x
    exact smul_add _ _ _
  rw [ha]
  abel

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
