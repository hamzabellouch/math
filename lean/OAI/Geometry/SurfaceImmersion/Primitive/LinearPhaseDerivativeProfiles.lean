import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateQuadraticExpansion
import OAI.Geometry.Immersion.ClosedSurface.AtlasPhases
import OAI.Geometry.SurfaceImmersion.Correction.WeightedPolynomialBounds

namespace OAI

/-! All derivatives of a fixed linear phase are constant fields.  The two
profiles needed by local quadratic cancellation are therefore uniform in
the derivative order, the map and both scales. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

def originalPhaseLinear (ξ : SmallModes.Base) : Base →L[ℝ] ℝ :=
  (phaseLinear ξ).comp planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap

lemma phase_eq_originalPhaseLinear {φ : Base → ℝ} {ξ : SmallModes.Base}
    (hphase : coordinatePhase φ = phaseLinear ξ) : φ = originalPhaseLinear ξ := by
  funext x
  change φ x = phaseLinear ξ (planeCoordinateIsometry x)
  simpa only [coordinatePhase,Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
    using congrFun hphase (planeCoordinateIsometry x)

lemma linear_phase_original_derivative {φ : Base → ℝ} {ξ : SmallModes.Base}
    (hphase : coordinatePhase φ = phaseLinear ξ) (v : Base) :
    (fun x => fderiv ℝ φ x v) = fun _ => originalPhaseLinear ξ v := by
  rw [phase_eq_originalPhaseLinear hphase]
  funext x
  exact congrArg (fun L : Base →L[ℝ] ℝ => L v) (originalPhaseLinear ξ).fderiv

lemma linear_phase_coordinate_derivative {φ : Base → ℝ} {ξ : SmallModes.Base}
    (hphase : coordinatePhase φ = phaseLinear ξ) (v : SmallModes.Base) :
    SmallModes.coordDeriv v (coordinatePhase φ) = fun _ => phaseLinear ξ v := by
  rw [hphase]
  funext x
  exact congrArg (fun L : SmallModes.Base →L[ℝ] ℝ => L v) (phaseLinear ξ).fderiv

/-- Fixed finite linear phases provide the original-coordinate and
mode-coordinate derivative bounds, including any additional input order. -/
theorem linear_phase_derivative_profiles {ι : Type*} [Fintype ι]
    (φ : ι → Base → ℝ) (ξ : ι → SmallModes.Base)
    (hphase : ∀ i, coordinatePhase (φ i) = phaseLinear (ξ i)) :
    ∃ F M : ℕ → ℝ, (∀ m, 1 ≤ F m) ∧ (∀ m, 1 ≤ M m) ∧
      (∀ (U : Set Base) (s : ℝ) (m r : ℕ) (i : ι) (v : Fin 2),
        WeightedBound U s (m + r) (F m)
          (fun x => fderiv ℝ (φ i) x (coordinateVector v))) ∧
      (∀ (s : ℝ) (m : ℕ) (i : ι) (v : SmallModes.Base), ‖v‖ ≤ 1 →
        WeightedBound Set.univ s m (M m) (SmallModes.coordDeriv v (coordinatePhase (φ i)))) := by
  classical
  let F₀ : ℝ := 1 + ∑ i, ‖originalPhaseLinear (ξ i)‖
  let M₀ : ℝ := 1 + ∑ i, ‖phaseLinear (ξ i)‖
  have hF (i : ι) : ‖originalPhaseLinear (ξ i)‖ ≤ F₀ :=
    (Finset.single_le_sum (fun j _ => norm_nonneg (originalPhaseLinear (ξ j)))
      (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
  have hM (i : ι) : ‖phaseLinear (ξ i)‖ ≤ M₀ :=
    (Finset.single_le_sum (fun j _ => norm_nonneg (phaseLinear (ξ j)))
      (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨(fun _ => F₀),(fun _ => M₀),?_,?_,?_,?_⟩
  · intro _
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => norm_nonneg _))
  · intro _
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => norm_nonneg _))
  · intro U s m r i v
    rw [linear_phase_original_derivative (hphase i)]
    apply (weightedBound_const U s (m + r) (originalPhaseLinear (ξ i) (coordinateVector v))).mono_const
    exact ((originalPhaseLinear (ξ i)).le_opNorm _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (norm_coordinateVector_le v)).trans (hF i))
  · intro s m i v hv
    rw [linear_phase_coordinate_derivative (hphase i)]
    apply (weightedBound_const Set.univ s m (phaseLinear (ξ i) v)).mono_const
    exact ((phaseLinear (ξ i)).le_opNorm v).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hv).trans (hM i))

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
