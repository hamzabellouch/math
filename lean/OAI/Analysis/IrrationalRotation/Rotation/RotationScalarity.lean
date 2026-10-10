import OAI.Analysis.IrrationalRotation.Rotation.RotationFieldExistence
import OAI.Analysis.IrrationalRotation.Rotation.ActualRotationCentrality
import OAI.Analysis.IrrationalRotation.Analysis.ScalarFieldLift
import OAI.Analysis.IrrationalRotation.Operators.RepresentedCommutation
import OAI.Analysis.IrrationalRotation.Analysis.FieldCovariance
import OAI.Analysis.IrrationalRotation.Model.OperatorProperties

namespace OAI

namespace Invariant233.Rotation

open MeasureTheory Filter
open scoped ENNReal

local notation "S" => LinearIsometry.toContinuousLinearMap
  (LinearIsometryEquiv.toLinearIsometry (WeightedShift.shift 1))

theorem scalar_of_represented_commute_and_covariance
    (θ : ℝ) (hθ : Irrational θ) (T : Hilbert →L[ℂ] Hilbert)
    (A : Circle → Fiber →L[ℂ] Fiber)
    (hm : ∀ v : Fiber, StronglyMeasurable fun x => A x v)
    (hrep : ∀ f : Hilbert, T f =ᵐ[circleMeasure] fun x => A x (f x))
    (hU : Commute T U) (hV : Commute T (V θ))
    (hcov : ∀ᵐ x ∂circleMeasure, S * A (x + (θ : Circle)) = A x * S) :
    ∃ c : ℂ, T = c • (1 : Hilbert →L[ℂ] Hilbert) := by
  let b : HilbertBasis ℤ ℂ Fiber :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fiber)
  have hAS : ∀ᵐ x ∂circleMeasure, Commute (A x) S :=
    DirectIntegral.ae_commute_of_represented_commute b T U A (fun _ => S)
      hrep U_ae hU
  have hAD : ∀ᵐ x ∂circleMeasure,
      Commute (A x) (WeightedShift.diagonal (orbitWeight θ character x)) :=
    DirectIntegral.ae_commute_of_represented_commute b T (V θ) A
      (fun x => WeightedShift.diagonal (orbitWeight θ character x))
      hrep (representation_ae θ character) hV
  have hmeas : NullMeasurable
      (fun x => A x (lp.single 2 (0 : ℤ) (1 : ℂ)) 0) circleMeasure := by
    exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).continuous.comp_stronglyMeasurable
      (hm (lp.single 2 (0 : ℤ) (1 : ℂ)))).measurable.nullMeasurable
  apply DirectIntegral.scalar_of_representation_ae_scalar T A hrep
  apply WeightedShift.ae_eq_scalar_over_circle_rotation θ hθ A
    (orbitWeight θ character) _ hmeas hAD hAS hcov
  exact Filter.Eventually.of_forall fun x k => by
    simp only [orbitWeight_apply, character, fourier_one, action]

theorem algebra_commutes_shiftedPullback (θ : ℝ)
    (T : Hilbert →L[ℂ] Hilbert) (hT : T ∈ algebra θ) :
    Commute T (DirectIntegral.shiftedPullback S (action θ 1)
      (action_measurePreserving θ 1)) := by
  let J := DirectIntegral.shiftedPullback S (action θ 1) (action_measurePreserving θ 1)
  have hUJ : Commute U J := by
    apply FieldTraceCyclic.commute_shiftedPullback_of_covariance U (fun _ => S)
      S (action θ 1) (action_measurePreserving θ 1) U_ae
    exact Filter.Eventually.of_forall fun _ => rfl
  have hVJ : Commute (V θ) J := by
    apply FieldTraceCyclic.commute_shiftedPullback_of_covariance (V θ)
      (fun x => WeightedShift.diagonal (orbitWeight θ character x))
      S (action θ 1) (action_measurePreserving θ 1) (representation_ae θ character)
    apply Filter.Eventually.of_forall
    intro x
    ext v k
    change character (action θ k x) * v (k - 1) =
      character (action θ (k - 1) (action θ 1 x)) * v (k - 1)
    simp only [action_add, sub_add_cancel]
  have hJ : J ∈ (algebra θ).commutant := by
    apply (mem_commutant_vonNeumannGenerated_iff _ _).mpr
    intro B hB
    rcases Set.mem_insert_iff.mp hB with rfl | hB
    · exact ⟨hUJ.eq, (commute_star_left_of_mem_unitary U_mem_unitary hUJ).eq⟩
    · have hBV : B = V θ := Set.mem_singleton_iff.mp hB
      subst B
      exact ⟨hVJ.eq, (commute_star_left_of_mem_unitary (V_mem_unitary θ) hVJ).eq⟩
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hJ) T hT

theorem scalar_of_mem_algebra_commute_generators
    (θ : ℝ) (hθ : Irrational θ) (T : Hilbert →L[ℂ] Hilbert)
    (hT : T ∈ algebra θ) (hU : Commute T U) (hV : Commute T (V θ)) :
    ∃ c : ℂ, T = c • (1 : Hilbert →L[ℂ] Hilbert) := by
  let : TopologicalSpace.SeparableSpace Fiber := HilbertModelSize.separable_l2 ℤ
  obtain ⟨A, hbound, hm, hrep, huniq⟩ := exists_unique_field_of_mem_algebra θ T hT
  have hcov := FieldTraceCyclic.ae_covariance_of_commute T
    (DirectIntegral.shiftedPullback S (action θ 1) (action_measurePreserving θ 1))
    A S (action θ 1) (action_measurePreserving θ 1) hrep
    (FieldTraceCyclic.shiftedPullback_ae S (action θ 1) (action_measurePreserving θ 1))
    (algebra_commutes_shiftedPullback θ T hT)
  apply scalar_of_represented_commute_and_covariance θ hθ T A hm hrep hU hV
  filter_upwards [hcov] with x hx
  simpa only [action, one_zsmul] using hx.symm

theorem algebra_isFactor (θ : ℝ) (hθ : Irrational θ) : IsFactor (algebra θ) := by
  constructor
  · by_contra h
    let : Subsingleton Hilbert := not_nontrivial_iff_subsingleton.mp h
    exact HilbertModelSize.circle_representation_not_finiteDimensional inferInstance
  · intro T hT hc
    apply scalar_of_mem_algebra_commute_generators θ hθ T hT
    · exact hc U (subset_vonNeumannGenerated _ (by simp))
    · exact hc (V θ) (subset_vonNeumannGenerated _ (by simp))

end Invariant233.Rotation

end OAI
