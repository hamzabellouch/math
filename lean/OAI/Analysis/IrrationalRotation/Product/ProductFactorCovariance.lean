import OAI.Analysis.IrrationalRotation.Product.ProductFields
import OAI.Analysis.IrrationalRotation.Rotation.FieldDiagonal
import OAI.Analysis.IrrationalRotation.Analysis.ScalarMultiplierFields
import OAI.Analysis.IrrationalRotation.Analysis.GeneratedVonNeumann
import OAI.Analysis.IrrationalRotation.Analysis.FieldCovariance
import OAI.Analysis.IrrationalRotation.Product.ProductBaseDynamics

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Invariant233.ProductModel

local notation "S" => LinearIsometry.toContinuousLinearMap
  (LinearIsometryEquiv.toLinearIsometry (WeightedShift.shift 1))

theorem multiplier_star (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) :
    star (multiplier θ g C hC hg hb) =
      multiplier θ (fun x => star (g x)) C hC (continuous_star.measurable.comp hg)
        (fun x => (norm_star (g x)).le.trans (hb x)) := by
  symm
  apply WeightedShift.fieldDiagonal_star_of_eq
  exact Eventually.of_forall fun x => by
    ext k
    rfl

private theorem commute_star_of_unitary {A B : Hilbert →L[ℂ] Hilbert}
    (hA : A ∈ unitary (Hilbert →L[ℂ] Hilbert)) (hAB : Commute A B) :
    Commute (star A) B := by
  obtain ⟨h₁, h₂⟩ := Unitary.mem_iff.mp hA
  show star A * B = B * star A
  calc
    star A * B = star A * (B * (A * star A)) := by rw [h₂, mul_one]
    _ = star A * ((A * B) * star A) := by rw [← mul_assoc B A, ← hAB.eq]
    _ = (star A * A) * (B * star A) := by simp only [mul_assoc]
    _ = B * star A := by rw [h₁, one_mul]

theorem rotationIterate_comp (θ : ℕ → ℝ) (m n : ℤ) (x : Base) :
    rotationIterate θ n (rotationIterate θ m x) = rotationIterate θ (m + n) x := by
  funext i
  simp only [rotationIterate, Int.cast_add, add_mul, AddCircle.coe_add, add_assoc]

theorem factor_commutes_shiftedPullback (θ : ℕ → ℝ) (r : ℤ)
    (T : Hilbert →L[ℂ] Hilbert) (hT : T ∈ factor θ) :
    Commute T (DirectIntegral.shiftedPullback
      (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap
      (rotationIterate θ r) (measurePreserving_rotationIterate θ r)) := by
  let Sr := (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap
  let J := DirectIntegral.shiftedPullback Sr (rotationIterate θ r)
    (measurePreserving_rotationIterate θ r)
  have hSJ : Commute shiftOperator J := by
    apply FieldTraceCyclic.commute_shiftedPullback_of_covariance
      shiftOperator (fun _ => S) Sr (rotationIterate θ r)
      (measurePreserving_rotationIterate θ r) shiftOperator_ae
    apply Eventually.of_forall
    intro x
    dsimp [Sr]
    rw [← WeightedShift.shift_add, ← WeightedShift.shift_add, add_comm]
  have hDJ (g : Base → ℂ) (C : ℝ) (hC : 0 ≤ C)
      (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) :
      Commute (multiplier θ g C hC hg hb) J := by
    apply FieldTraceCyclic.commute_shiftedPullback_of_covariance
      (multiplier θ g C hC hg hb)
      (fun x => WeightedShift.diagonal (multiplierField θ g C hb x))
      Sr (rotationIterate θ r) (measurePreserving_rotationIterate θ r)
      (multiplier_ae θ g C hC hg hb)
    apply Eventually.of_forall
    intro x
    ext v k
    change g (rotationIterate θ k x) * v (k - r) =
      g (rotationIterate θ (k - r) (rotationIterate θ r x)) * v (k - r)
    rw [rotationIterate_comp]
    congr 3
    omega
  have hJ : J ∈ (factor θ).commutant := by
    apply (mem_commutant_vonNeumannGenerated_iff _ _).mpr
    intro A hA
    rcases hA with hA | hA
    · have hA' : A = shiftOperator := Set.mem_singleton_iff.mp hA
      subst A
      exact ⟨hSJ.eq,
        (commute_star_of_unitary (WeightedShift.fieldShift_mem_unitary 1) hSJ).eq⟩
    · obtain ⟨g, C, hC, hg, hb, rfl⟩ := hA
      refine ⟨(hDJ g C hC hg hb).eq, ?_⟩
      rw [multiplier_star]
      exact (hDJ _ C hC _ _).eq
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hJ) T hT

theorem ae_covariance_of_mem_factor (θ : ℕ → ℝ)
    (T : Hilbert →L[ℂ] Hilbert) (hT : T ∈ factor θ)
    (A : Base → Fiber →L[ℂ] Fiber)
    (hrep : ∀ f : Hilbert, T f =ᵐ[baseMeasure] fun x => A x (f x)) (r : ℤ) :
    ∀ᵐ x ∂baseMeasure,
      A x * (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap =
        (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap *
          A (rotationIterate θ r x) := by
  let : TopologicalSpace.SeparableSpace Fiber := HilbertModelSize.separable_l2 ℤ
  exact FieldTraceCyclic.ae_covariance_of_commute T _ A _ _
    (measurePreserving_rotationIterate θ r) hrep
    (FieldTraceCyclic.shiftedPullback_ae _ _ _)
    (factor_commutes_shiftedPullback θ r T hT)

end Invariant233.ProductModel

end

end OAI
