import OAI.Geometry.SurfaceImmersion.Correction.AtlasModeGerms
import OAI.Geometry.SurfaceImmersion.Correction.MixedPolynomialLocality

namespace OAI

/-! The genuine quadratic polynomial of a global mode sum has the usual
mean and nonzero-phase expansion in each active chart. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem local_mode_polynomial_quadratic {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (i : A.centers)
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → JetPolynomial.Space)
    (τ : ℝ) (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j))
    {x : Base} (hx : A.chartWeight i x ≠ 0) :
    let φlocal := fun j => A.vectorChartRead i (φ j)
    let Zlocal := fun j => A.vectorChartRead i (Z j)
    coordinateQuadraticPolynomial P ε G
        (A.jetChartMap i (spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)) ∘
          planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x) =
      coordinateQuadraticMean P ε G φlocal Zlocal τ 0 (planeCoordinateIsometry x)+
        ∑ l : RealModes.QuadraticLabel ι,
          QuadraticMean.displacement τ
            (RealModes.quadraticPhase (fun j => coordinatePhase (φlocal j)) l)
            (coordinateQuadraticCoefficient P ε G φlocal Zlocal τ 0 l)
            (planeCoordinateIsometry x) := by
  dsimp only
  let V := QuadraticMean.sumDisplacement τ
    (fun j => coordinatePhase (A.vectorChartRead i (φ j)))
    (fun j => coordinateAmplitude (A.vectorChartRead i (Z j)))
  have hg :
      (A.jetChartMap i (spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)) ∘
        planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry =ᶠ[𝓝 x]
          V ∘ planeCoordinateIsometry := by
    have hh := A.jetChartMap_modes_germ i τ φ Z hx
    simpa only [Function.comp_def,planeCoordinateIsometry.symm_apply_apply,V] using hh
  rw [coordinateQuadraticPolynomial_eq_of_eventuallyEq P ε G hg 0]
  exact congrFun (coordinate_quadratic_polynomial_expansion P ε G
    (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j))
    (fun j => A.vectorChartRead_smooth i (hφ j))
    (fun j => A.vectorChartRead_smooth i (hZ j)) τ 0) (planeCoordinateIsometry x)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
