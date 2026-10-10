import OAI.Analysis.IrrationalRotation.Rotation.RotationFieldRepresentation
import OAI.Analysis.IrrationalRotation.Rotation.RotationAlgebra
import OAI.Analysis.IrrationalRotation.Rotation.RotationHilbert
import OAI.Analysis.IrrationalRotation.Rotation.WeightedShiftCentrality
import OAI.Analysis.IrrationalRotation.Operators.RepresentedFieldCommutation
import OAI.Analysis.IrrationalRotation.Analysis.FieldKoopmanGenerated
import OAI.Analysis.IrrationalRotation.Analysis.ScalarFieldLift
import OAI.Analysis.IrrationalRotation.Model.OperatorProperties

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.Rotation

local notation "S" => LinearIsometry.toContinuousLinearMap
  (LinearIsometryEquiv.toLinearIsometry (WeightedShift.shift 1))

theorem algebra_commutes_shiftedPullback_int_independent (θ : ℝ) (m : ℤ)
    {T : Hilbert →L[ℂ] Hilbert} (hT : T ∈ algebra θ) :
    Commute T (DirectIntegral.shiftedPullback
      (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap
      (action θ m) (action_measurePreserving θ m)) := by
  apply FieldKoopman.commute_of_mem_generated_of_unitary
    ({U, V θ} : Set (Hilbert →L[ℂ] Hilbert))
    (FieldKoopman.operator_mem_unitary (WeightedShift.shift m)
      (action θ m) (action θ (-m))
      (action_measurePreserving θ m) (action_measurePreserving θ (-m))
      (by funext x; simp)
      (by funext x; simp)) _ hT
  intro B hB
  rcases Set.mem_insert_iff.mp hB with rfl | hB
  · exact FieldKoopman.commute_fieldShifts 1 m (action θ m)
      (action_measurePreserving θ m)
  · have hB' : B = V θ := Set.mem_singleton_iff.mp hB
    subst B
    apply FieldKoopman.commute_fieldDiagonal
      (orbitWeight θ character) ‖character‖ (norm_nonneg character)
      (fun x => orbitWeight_norm_le θ character x)
      (fun k => (character.continuous.comp (action_continuous θ k)).aestronglyMeasurable)
      m (action θ m) (action_measurePreserving θ m)
    exact Filter.Eventually.of_forall fun x k => by
      simp only [orbitWeight_apply, action_add, sub_add_cancel]

theorem central_eq_scalar (θ : ℝ) (hθ : Irrational θ)
    {T : Hilbert →L[ℂ] Hilbert} (hT : T ∈ algebra θ)
    (hcentral : ∀ B : Hilbert →L[ℂ] Hilbert, B ∈ algebra θ → Commute T B) :
    ∃ c : ℂ, T = c • (1 : Hilbert →L[ℂ] Hilbert) := by
  obtain ⟨F, hbound, hmeas, hrep, huniq⟩ := exists_unique_field hT
  let b : HilbertBasis ℤ ℂ Fiber := default
  have hS : ∀ᵐ x ∂circleMeasure, Commute (F x) S :=
    DirectIntegral.ae_commute_of_representations b T U F (fun _ => S)
      hrep U_ae (hcentral U (U_mem_algebra θ))
  have hD : ∀ᵐ x ∂circleMeasure,
      Commute (F x) (WeightedShift.diagonal (orbitWeight θ character x)) :=
    DirectIntegral.ae_commute_of_representations b T (V θ) F
      (fun x => WeightedShift.diagonal (orbitWeight θ character x))
      hrep (representation_ae θ character) (hcentral (V θ) (V_mem_algebra θ))
  have hcov : ∀ᵐ x ∂circleMeasure, S * F (action θ 1 x) = F x * S := by
    filter_upwards [DirectIntegral.ae_covariance_of_represented_commute b T F S
      (action θ 1) (action_measurePreserving θ 1) hrep
      (algebra_commutes_shiftedPullback_int_independent θ 1 hT)] with x hx
    exact hx.symm
  have hm : NullMeasurable
      (fun x => F x (lp.single 2 (0 : ℤ) (1 : ℂ)) 0) circleMeasure :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).continuous.comp_stronglyMeasurable
      (hmeas (lp.single 2 (0 : ℤ) (1 : ℂ)))).measurable.nullMeasurable
  obtain ⟨c, hc⟩ := WeightedShift.ae_eq_scalar_of_commute_irrational_diagonal_shift
    circleMeasure (action θ 1) (action_one_ergodic hθ) F
    (orbitWeight θ character) θ hθ id
    (Filter.Eventually.of_forall fun x k => by
      simp [orbitWeight_apply, character, fourier_apply, action]) hm hD hS hcov
  exact ⟨c, DirectIntegral.eq_smul_id_of_representation_ae_scalar T F hrep c hc⟩

theorem algebra_isFactor_independent (θ : ℝ) (hθ : Irrational θ) : IsFactor (algebra θ) := by
  refine ⟨inferInstance, ?_⟩
  intro T hT hcentral
  exact central_eq_scalar θ hθ hT hcentral

end Invariant233.Rotation

end

end OAI
