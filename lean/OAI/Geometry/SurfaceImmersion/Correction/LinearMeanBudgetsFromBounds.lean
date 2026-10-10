import OAI.Geometry.SurfaceImmersion.Atlas.LinearPhaseDerivativeBounds
import OAI.Geometry.SurfaceImmersion.Geometry.TensorPullbackNorm
import OAI.Geometry.SurfaceImmersion.Correction.LinearPhaseMeanGeometry
import OAI.Geometry.Immersion.ClosedSurface.LocalMean
import OAI.Geometry.SurfaceImmersion.Correction.WeightedPolynomialBounds

namespace OAI

/-! Actual mean budgets in a linear phase chart, with all geometric
constants specified by operator norms and supplied field bounds. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes PhaseGeometry WeightedEstimates

noncomputable def linearMeanBudgetsOfBounds
    {U : Set Base} (hU : IsOpen U) {ξ : Base} (hξ : ξ ≠ 0)
    (s : ℝ) (F : RField 4) (ψ : Base → ℝ) (Q : Tensor →L[ℝ] ℝ)
    (C N P : ℕ → ℝ) (hC : ∀ m, 1 ≤ C m) (hN : ∀ m, 1 ≤ N m) (hP : ∀ m, 1 ≤ P m)
    (hc : ∀ m, ReconstructionCoefficientBound (fun x => complexify (F x))
      (linearPhaseChart ξ hξ U hU).target s m (C m))
    (hn : ∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s m (N m) (freeNormal F))
    (hψ : ∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s m (P m) ψ) :
    Budgets U (linearPhaseChart ξ hξ U hU).target s F ψ (fun _ => Q)
      (linearPhaseChart ξ hξ U hU) (linearPhaseChart ξ hξ U hU).symm where
  inv := fun _ => max 1 ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖
  chi := fun _ => max 1 (2*‖ξ‖)
  forms := fun _ => max 1 ‖Q‖
  pull := fun _ => max 1 (16*‖ξ‖^2)
  psi := P
  normal := N
  mode := C
  inv_pos := fun _ => le_max_left _ _
  chi_pos := fun _ => le_max_left _ _
  forms_pos := fun _ => le_max_left _ _
  pull_pos := fun _ => le_max_left _ _
  psi_pos := hP
  normal_pos := hN
  mode_pos := hC
  inv_bound := by
    intro m j hj _ x hx
    exact (positive_order_linear_derivative_le (phaseEquiv ξ hξ).symm.toContinuousLinearMap
      (linearPhaseChart ξ hξ U hU).open_target hj hx).trans (le_max_right _ _)
  chi_bound := by
    intro m j hj _ x hx
    exact (linearPhaseChart_derivative_bound hξ hU hj hx).trans (le_max_right _ _)
  psi_bound := hψ
  normal_bound := hn
  mode_bound := hc
  forms_bound := fun m => (weightedBound_const _ s m Q).mono_const (le_max_right _ _)
  pull_bound := by
    intro m
    have hL := phaseEquiv_norm_le ξ hξ
    have hP : ‖pullback (phaseEquiv ξ hξ).toContinuousLinearMap‖ ≤ 16*‖ξ‖^2 := by
      have hsq := pow_le_pow_left₀ (norm_nonneg (phaseEquiv ξ hξ).toContinuousLinearMap) hL 2
      exact (norm_pullback_le _).trans (by nlinarith [hsq])
    have he : pullbackField (linearPhaseChart ξ hξ U hU) =
        fun _ => pullback (phaseEquiv ξ hξ).toContinuousLinearMap :=
      funext (pullbackField_linearPhaseChart hξ hU)
    rw [he]
    exact (weightedBound_const U s m _).mono_const (hP.trans (le_max_right _ _))

end ClosedSurfaceR4.PhaseMean

end

end OAI
