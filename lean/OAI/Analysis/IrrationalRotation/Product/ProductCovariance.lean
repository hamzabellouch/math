import OAI.Analysis.IrrationalRotation.Product.ProductFields
import OAI.Analysis.IrrationalRotation.Product.ProductCocycle
import OAI.Analysis.IrrationalRotation.Analysis.FieldKoopmanGenerated
import OAI.Analysis.IrrationalRotation.Analysis.FieldCovariance

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.ProductModel

@[simp] theorem rotationIterate_zero (θ : ℕ → ℝ) (x : Base) :
    rotationIterate θ 0 x = x := ProductCocycle.rotate_zero θ x

theorem rotationIterate_add (θ : ℕ → ℝ) (m n : ℤ) (x : Base) :
    rotationIterate θ (m + n) x = rotationIterate θ n (rotationIterate θ m x) :=
  ProductCocycle.rotate_add θ m n x

theorem rotationIterate_measurePreserving (θ : ℕ → ℝ) (m : ℤ) :
    MeasurePreserving (rotationIterate θ m) baseMeasure baseMeasure :=
  ProductCocycle.measurePreserving_rotate θ m

theorem shiftedPullback_mem_unitary (θ : ℕ → ℝ) (m : ℤ) :
    DirectIntegral.shiftedPullback
      (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap
      (rotationIterate θ m) (rotationIterate_measurePreserving θ m) ∈
        unitary (Hilbert →L[ℂ] Hilbert) := by
  apply FieldKoopman.operator_mem_unitary (WeightedShift.shift m)
    (rotationIterate θ m) (rotationIterate θ (-m))
  · exact rotationIterate_measurePreserving θ (-m)
  · funext x
    change rotationIterate θ (-m) (rotationIterate θ m x) = x
    rw [← rotationIterate_add]
    simp
  · funext x
    change rotationIterate θ m (rotationIterate θ (-m) x) = x
    rw [← rotationIterate_add]
    simp

theorem multiplier_commutes_shiftedPullback (θ : ℕ → ℝ)
    (g : Base → ℂ) (C : ℝ) (hC : 0 ≤ C) (hg : Measurable g)
    (hb : ∀ x, ‖g x‖ ≤ C) (m : ℤ) :
    Commute (multiplier θ g C hC hg hb)
      (DirectIntegral.shiftedPullback
        (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap
        (rotationIterate θ m) (rotationIterate_measurePreserving θ m)) := by
  unfold multiplier
  apply FieldKoopman.commute_fieldDiagonal
  apply Filter.Eventually.of_forall
  intro x k
  change g (rotationIterate θ (k - m) (rotationIterate θ m x)) =
    g (rotationIterate θ k x)
  rw [← rotationIterate_add]
  congr 2
  omega

theorem commute_shiftedPullback_of_mem_factor (θ : ℕ → ℝ)
    {T : Hilbert →L[ℂ] Hilbert} (hT : T ∈ factor θ) (m : ℤ) :
    Commute T (DirectIntegral.shiftedPullback
      (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap
      (rotationIterate θ m) (rotationIterate_measurePreserving θ m)) := by
  apply FieldKoopman.commute_of_mem_generated_of_unitary
    ({shiftOperator} ∪ multiplierGenerators θ) (shiftedPullback_mem_unitary θ m) _ hT
  intro A hA
  rcases hA with hA | hA
  · rcases Set.mem_singleton_iff.mp hA with rfl
    exact FieldKoopman.commute_fieldShifts 1 m _ _
  · obtain ⟨g, C, hC, hg, hb, rfl⟩ := hA
    exact multiplier_commutes_shiftedPullback θ g C hC hg hb m

theorem field_matrix_covariance {θ : ℕ → ℝ} {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ factor θ) (F : Base → Fiber →L[ℂ] Fiber)
    (hF : ∀ ξ : Hilbert, T ξ =ᵐ[baseMeasure] fun x => F x (ξ x)) :
    ∀ m k l : ℤ, ∀ᵐ x ∂baseMeasure,
      inner ℂ ((default : HilbertBasis ℤ ℂ Fiber) k)
        (F (rotationIterate θ m x) ((default : HilbertBasis ℤ ℂ Fiber) l)) =
      inner ℂ ((default : HilbertBasis ℤ ℂ Fiber) (k + m))
        (F x ((default : HilbertBasis ℤ ℂ Fiber) (l + m))) := by
  apply FieldTraceCyclic.ae_matrix_covariance_of_commute
    (default : HilbertBasis ℤ ℂ Fiber) T F
    (fun m => DirectIntegral.shiftedPullback
      (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap
      (rotationIterate θ m) (rotationIterate_measurePreserving θ m))
    (fun m => (WeightedShift.shift m).toLinearIsometry)
    (rotationIterate θ) (rotationIterate_measurePreserving θ)
  · exact FieldKoopman.shift_default_basis
  · exact hF
  · intro m
    exact FieldTraceCyclic.shiftedPullback_ae _ _ _
  · exact commute_shiftedPullback_of_mem_factor θ hT

theorem field_covariance {θ : ℕ → ℝ} {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ factor θ) (F : Base → Fiber →L[ℂ] Fiber)
    (hF : ∀ ξ : Hilbert, T ξ =ᵐ[baseMeasure] fun x => F x (ξ x)) :
    ∀ᵐ x ∂baseMeasure, ∀ m : ℤ,
      F x * (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap =
        (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap *
          F (rotationIterate θ m x) := by
  let := HilbertModelSize.separable_of_countable_hilbertBasis
    (default : HilbertBasis ℤ ℂ Fiber)
  apply ae_all_iff.mpr
  intro m
  exact FieldTraceCyclic.ae_covariance_of_commute T _ F _ _
    (rotationIterate_measurePreserving θ m) hF
    (FieldTraceCyclic.shiftedPullback_ae _ _ _)
    (commute_shiftedPullback_of_mem_factor θ hT m)

theorem field_conjugacy {θ : ℕ → ℝ} {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ factor θ) (F : Base → Fiber →L[ℂ] Fiber)
    (hF : ∀ ξ : Hilbert, T ξ =ᵐ[baseMeasure] fun x => F x (ξ x)) :
    ∀ᵐ x ∂baseMeasure, ∀ m : ℤ,
      F (rotationIterate θ m x) =
        (WeightedShift.shift (-m)).toLinearIsometry.toContinuousLinearMap * F x *
          (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap := by
  filter_upwards [field_covariance hT F hF] with x hx m
  have hinv : (WeightedShift.shift (-m)).toLinearIsometry.toContinuousLinearMap *
      (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap = 1 := by
    rw [← WeightedShift.shift_add]
    simp [WeightedShift.shift_zero]
  have heq := congrArg
    (fun A : Fiber →L[ℂ] Fiber =>
      (WeightedShift.shift (-m)).toLinearIsometry.toContinuousLinearMap * A) (hx m)
  simpa only [← mul_assoc, hinv, one_mul] using heq.symm

end Invariant233.ProductModel

end

end OAI
