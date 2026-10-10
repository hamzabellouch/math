import OAI.Analysis.IrrationalRotation.Analysis.FieldCentrality
import OAI.Analysis.IrrationalRotation.Rotation.WeightedShiftPowers

namespace OAI

namespace Invariant233.WeightedShift

open MeasureTheory Filter

local notation "S" =>
  LinearIsometry.toContinuousLinearMap (LinearIsometryEquiv.toLinearIsometry (shift 1))

theorem forwardShift_single (j : ℤ) :
    S (lp.single 2 j (1 : ℂ)) = lp.single 2 (j + 1) (1 : ℂ) := by
  ext k
  change shift 1 (lp.single 2 j (1 : ℂ)) k =
    lp.single (E := fun _ : ℤ => ℂ) 2 (j + 1) (1 : ℂ) k
  rw [shift_apply]
  by_cases hk : k = j + 1
  · subst k
    simp
  · have hk' : k - 1 ≠ j := by omega
    simp [lp.single_apply, hk, hk']

theorem scalar_of_commute_diagonal_shift
    (A : Hilbert →L[ℂ] Hilbert) (w : Weight) (hw : Function.Injective w)
    (hD : Commute A (diagonal w)) (hS : Commute A S) :
    ∃ c : ℂ, A = c • (1 : Hilbert →L[ℂ] Hilbert) := by
  exact FiberCentrality.scalar_of_commute_diagonal_and_shift
    A (diagonal w) S w hw (diagonal_apply w) forwardShift_single hD.eq hS.eq

theorem ae_eq_scalar_of_commute_diagonal_shift
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (σ : X → X)
    (hσ : Ergodic σ μ) (A : X → Hilbert →L[ℂ] Hilbert) (w : X → Weight)
    (hm : NullMeasurable (fun x => A x (lp.single 2 (0 : ℤ) (1 : ℂ)) 0) μ)
    (hw : ∀ᵐ x ∂μ, Function.Injective (w x))
    (hD : ∀ᵐ x ∂μ, Commute (A x) (diagonal (w x)))
    (hS : ∀ᵐ x ∂μ, Commute (A x) S)
    (hcov : ∀ᵐ x ∂μ, S * A (σ x) = A x * S) :
    ∃ c : ℂ, ∀ᵐ x ∂μ, A x = c • (1 : Hilbert →L[ℂ] Hilbert) := by
  apply FiberCentrality.ae_eq_scalar_of_ergodic_covariance
    μ σ hσ A S forwardShift_single hm _ hcov
  filter_upwards [hw, hD, hS] with x hwx hDx hSx
  exact scalar_of_commute_diagonal_shift (A x) (w x) hwx hDx hSx

theorem ae_eq_scalar_of_commute_irrational_diagonal_shift
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (σ : X → X)
    (hσ : Ergodic σ μ) (A : X → Hilbert →L[ℂ] Hilbert) (w : X → Weight)
    (θ : ℝ) (hθ : Irrational θ) (x₀ : X → AddCircle (1 : ℝ))
    (hphase : ∀ᵐ x ∂μ, ∀ k : ℤ,
      w x k = (AddCircle.toCircle (x₀ x + k • (θ : AddCircle (1 : ℝ))) : ℂ))
    (hm : NullMeasurable (fun x => A x (lp.single 2 (0 : ℤ) (1 : ℂ)) 0) μ)
    (hD : ∀ᵐ x ∂μ, Commute (A x) (diagonal (w x)))
    (hS : ∀ᵐ x ∂μ, Commute (A x) S)
    (hcov : ∀ᵐ x ∂μ, S * A (σ x) = A x * S) :
    ∃ c : ℂ, ∀ᵐ x ∂μ, A x = c • (1 : Hilbert →L[ℂ] Hilbert) := by
  apply ae_eq_scalar_of_commute_diagonal_shift μ σ hσ A w hm _ hD hS hcov
  filter_upwards [hphase] with x hx
  intro j k hjk
  apply FiberCentrality.injective_irrational_diagonal θ hθ (x₀ x)
  simpa only [hx] using hjk

end Invariant233.WeightedShift

end OAI
