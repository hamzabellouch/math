import OAI.Analysis.IrrationalRotation.Operators.CovariantTracialVector
import OAI.Analysis.IrrationalRotation.Rotation.RotationFieldRepresentation
import OAI.Analysis.IrrationalRotation.Rotation.RotationHilbert

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.Rotation

theorem algebra_commutes_shiftedPullback_int (θ : ℝ) (r : ℤ)
    (T : Hilbert →L[ℂ] Hilbert) (hT : T ∈ algebra θ) :
    Commute T (DirectIntegral.shiftedPullback
      (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap
      (action θ r) (action_measurePreserving θ r)) := by
  let S := (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap
  let S₁ := (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap
  let J := DirectIntegral.shiftedPullback S (action θ r) (action_measurePreserving θ r)
  have hUJ : Commute U J := by
    apply FieldTraceCyclic.commute_shiftedPullback_of_covariance U (fun _ => S₁)
      S (action θ r) (action_measurePreserving θ r) U_ae
    apply Filter.Eventually.of_forall
    intro x
    dsimp [S, S₁]
    rw [← WeightedShift.shift_add, ← WeightedShift.shift_add, add_comm (1 : ℤ) r]
  have hVJ : Commute (V θ) J := by
    apply FieldTraceCyclic.commute_shiftedPullback_of_covariance (V θ)
      (fun x => WeightedShift.diagonal (orbitWeight θ character x))
      S (action θ r) (action_measurePreserving θ r) (representation_ae θ character)
    apply Filter.Eventually.of_forall
    intro x
    ext v k
    change character (action θ k x) * v (k - r) =
      character (action θ (k - r) (action θ r x)) * v (k - r)
    simp only [action_add, sub_add_cancel]
  have hJ : J ∈ (algebra θ).commutant := by
    apply (mem_commutant_vonNeumannGenerated_iff _ _).mpr
    intro A hA
    rcases Set.mem_insert_iff.mp hA with rfl | hA
    · exact ⟨hUJ.eq, (commute_star_left_of_mem_unitary U_mem_unitary hUJ).eq⟩
    · have hAV : A = V θ := Set.mem_singleton_iff.mp hA
      subst A
      exact ⟨hVJ.eq, (commute_star_left_of_mem_unitary (V_mem_unitary θ) hVJ).eq⟩
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hJ) T hT

theorem field_covariance_int (θ : ℝ) (r : ℤ)
    (T : Hilbert →L[ℂ] Hilbert) (A : Circle → Fiber →L[ℂ] Fiber)
    (hT : T ∈ algebra θ)
    (hrep : ∀ ξ : Hilbert, T ξ =ᵐ[circleMeasure] fun x => A x (ξ x)) :
    ∀ᵐ x ∂circleMeasure,
      A x * (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap =
        (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap *
          A (action θ r x) := by
  let : TopologicalSpace.SeparableSpace Fiber := HilbertModelSize.separable_l2 ℤ
  exact FieldTraceCyclic.ae_covariance_of_commute T _ A
    (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap
    (action θ r) (action_measurePreserving θ r) hrep
    (FieldTraceCyclic.shiftedPullback_ae _ _ _)
    (algebra_commutes_shiftedPullback_int θ r T hT)

theorem exists_covariant_field {θ : ℝ} {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ algebra θ) :
    ∃ A : Circle → Fiber →L[ℂ] Fiber,
      (∀ x, ‖A x‖ ≤ ‖T‖) ∧
      (∀ v : Fiber, StronglyMeasurable fun x => A x v) ∧
      (∀ ξ : Hilbert, T ξ =ᵐ[circleMeasure] fun x => A x (ξ x)) ∧
      (∀ r : ℤ, ∀ᵐ x ∂circleMeasure,
        A x * (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap =
          (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap *
            A (action θ r x)) := by
  obtain ⟨A, hbound, hm, hrep, _⟩ := exists_unique_field hT
  exact ⟨A, hbound, hm, hrep, fun r => field_covariance_int θ r T A hT hrep⟩

theorem vacuumFunctional_eq_integral_of_field
    (T : Hilbert →L[ℂ] Hilbert) (A : Circle → Fiber →L[ℂ] Fiber)
    (hrep : ∀ ξ : Hilbert, T ξ =ᵐ[circleMeasure] fun x => A x (ξ x)) :
    vacuumFunctional T =
      ∫ x, inner ℂ (lp.single 2 (0 : ℤ) (1 : ℂ))
        (A x (lp.single 2 (0 : ℤ) (1 : ℂ))) ∂circleMeasure :=
  FieldTraceCyclic.constant_vector_state_eq_integral T A hrep _

theorem vacuum_faithfulTracial (θ : ℝ) :
    IsFaithfulTracialVector (algebra θ) vacuum := by
  let b : HilbertBasis ℤ ℂ Fiber :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fiber)
  have hb (k : ℤ) : b k = lp.single 2 k 1 := by
    rw [← HilbertBasis.repr_symm_single]
    rfl
  have hshift (r k : ℤ) :
      (WeightedShift.shift r).toLinearIsometry (b k) = b (k + r) := by
    rw [hb, hb]
    ext j
    change (lp.single 2 k (1 : ℂ) : Fiber) (j-r) = (lp.single 2 (k+r) (1 : ℂ) : Fiber) j
    simp only [lp.single_apply]
    simp only [Pi.single_apply]
    by_cases h : j - r = k
    · have h' : j = k + r := by omega
      rw [ite_eq_left h, ite_eq_left h']
    · have h' : j ≠ k + r := by omega
      rw [ite_eq_right h, ite_eq_right h']
  have h := FieldTraceCyclic.faithfulTracialVector_of_commuting_shiftedPullbacks
    b (algebra θ) (action θ) (action_measurePreserving θ)
    (fun r => (WeightedShift.shift r).toLinearIsometry) hshift
    (fun T hT r => algebra_commutes_shiftedPullback_int θ r T hT) ?_
  · simpa only [hb, vacuum] using h
  · intro T hT
    obtain ⟨A, hbound, hm, hrep, _⟩ := exists_unique_field hT
    exact ⟨A, hrep, fun r => (hm (b r)).aestronglyMeasurable,
      Filter.Eventually.of_forall hbound⟩

end Invariant233.Rotation

end

end OAI
