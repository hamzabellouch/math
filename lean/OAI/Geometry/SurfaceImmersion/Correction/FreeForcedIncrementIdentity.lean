import OAI.Geometry.SurfaceImmersion.Geometry.QuadraticInteraction
import OAI.Geometry.Immersion.ClosedSurface.ForcedSolve

namespace OAI

/-! Exact nonlinear error decomposition after the free oscillation and the
forced cancellation, for the actual metric plus polynomial perturbation. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

def combinedNonzeroQuadratic {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ : ℝ) :
    SmallModes.Base → PhaseMean.Tensor :=
  fun p => ∑ l : RealModes.QuadraticLabel ι,
    QuadraticMean.displacement τ
      (RealModes.quadraticPhase (fun i => coordinatePhase (φ i)) l)
      (combinedQuadraticCoefficient P ε G φ H τ 0 l) p

theorem free_forced_metric_increment_identity {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (hH : ∀ i, ContDiff ℝ ∞ (H i)) (τ : ℝ)
    {V : RealModes.RField 4} (hV : ContDiff ℝ ∞ V) (T : SmallModes.Base → PhaseMean.Tensor) :
    let U := QuadraticMean.sumDisplacement τ (fun i => coordinatePhase (φ i))
      (fun i => coordinateAmplitude (H i))
    coordinateMetricMap P ε (fun x => G x + (U + V) (planeCoordinateIsometry x)) -
      coordinateMetricMap P ε G - T =
      coordinateFullLinearized P ε G U +
      (coordinateFullLinearized P ε G V + combinedNonzeroQuadratic P ε G φ H τ) +
      (combinedQuadraticMean P ε G φ H τ 0 - T) +
      coordinateQuadraticInteraction P ε G U V + coordinateTaylorRemainder P ε G (U + V) := by
  let U := QuadraticMean.sumDisplacement τ (fun i => coordinatePhase (φ i))
    (fun i => coordinateAmplitude (H i))
  have hU : ContDiff ℝ ∞ U := by
    apply ContDiff.sum
    intro i hi
    exact contDiffOn_univ.mp (RealModes.contDiffOn_displacement
      ((hφ i).comp planeCoordinateIsometry.symm.contDiff).contDiffOn
      ((hH i).comp planeCoordinateIsometry.symm.contDiff).contDiffOn τ)
  have hquad : coordinateFullQuadratic P ε G U =
      combinedQuadraticMean P ε G φ H τ 0 + combinedNonzeroQuadratic P ε G φ H τ :=
    combined_quadratic_expansion P ε G φ H hφ hH τ 0
  have hUV : ContDiff ℝ ∞ (U + V) := hU.add hV
  dsimp only
  rw [coordinate_metric_taylor_identity P ε hG hUV,
    coordinateFullLinearized_add P ε G hU hV,
    coordinateFullQuadratic_add P ε G hU hV, hquad]
  funext p k
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
