import OAI.Analysis.IrrationalRotation.Model.Rotation

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.Rotation

theorem vacuumFunctional_representation (θ : ℝ) (a : C(Circle, ℂ)) :
    vacuumFunctional (representation θ a) = ∫ x, a x ∂circleMeasure := by
  change inner ℂ vacuum (representation θ a vacuum) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  have hv : vacuum =ᵐ[circleMeasure]
      fun _ => lp.single 2 (0 : ℤ) (1 : ℂ) := Lp.coeFn_const 2 circleMeasure _
  have hp : representation θ a vacuum =ᵐ[circleMeasure]
      fun x => WeightedShift.diagonal (orbitWeight θ a x) (vacuum x) := by
    unfold representation WeightedShift.fieldDiagonal WeightedShift.fieldDiagonalLinear
    exact WeightedShift.fieldDiagonalVec_ae (orbitWeight θ a) ‖a‖ (norm_nonneg a)
      (fun x => lp.norm_le_of_forall_le (norm_nonneg a) (fun k => a.norm_coe_le_norm _))
      (fun k => (a.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
      vacuum
  filter_upwards [hv, hp] with x hv hp
  rw [hp, hv, lp.inner_single_left]
  change inner ℂ (1 : ℂ) (a (action θ 0 x) * 1) = a x
  simp [action]

theorem vacuumFunctional_representation_real (θ : ℝ) (f : C(Circle, ℝ)) :
    vacuumFunctional (representation θ (complexWeight f)) =
      ∫ x, (f x : ℂ) ∂circleMeasure :=
  vacuumFunctional_representation θ (complexWeight f)

end Invariant233.Rotation

end

end OAI
