import OAI.Analysis.IrrationalRotation.Rotation.WeightedShiftCentrality
import OAI.Analysis.IrrationalRotation.Rotation.CircleErgodicity
import OAI.Analysis.IrrationalRotation.Product.ProductBaseDynamics

namespace OAI

namespace Invariant233.WeightedShift

open MeasureTheory Filter

local notation "S" =>
  LinearIsometry.toContinuousLinearMap (LinearIsometryEquiv.toLinearIsometry (shift 1))

theorem ae_eq_scalar_over_circle_rotation
    (θ : ℝ) (hθ : Irrational θ)
    (A : Invariant233.Circle → Hilbert →L[ℂ] Hilbert)
    (w : Invariant233.Circle → Weight)
    (hphase : ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      w x k = (AddCircle.toCircle (x + k • (θ : Invariant233.Circle)) : ℂ))
    (hm : NullMeasurable
      (fun x => A x (lp.single 2 (0 : ℤ) (1 : ℂ)) 0) circleMeasure)
    (hD : ∀ᵐ x ∂circleMeasure, Commute (A x) (diagonal (w x)))
    (hS : ∀ᵐ x ∂circleMeasure, Commute (A x) S)
    (hcov : ∀ᵐ x ∂circleMeasure,
      S * A (x + (θ : Invariant233.Circle)) = A x * S) :
    ∃ c : ℂ, ∀ᵐ x ∂circleMeasure,
      A x = c • (1 : Hilbert →L[ℂ] Hilbert) := by
  exact ae_eq_scalar_of_commute_irrational_diagonal_shift
    circleMeasure (fun x => x + (θ : Invariant233.Circle))
    (InvariantProjection.CircleErgodicity.irrational_rotation_ergodic hθ)
    A w θ hθ id hphase hm hD hS hcov

theorem ae_eq_scalar_over_product_rotation
    (θ : ℕ → ℝ) (hθ : ProductModel.JointlyRationallyIndependent θ)
    (i : ℕ) (A : ProductModel.Base → Hilbert →L[ℂ] Hilbert)
    (w : ProductModel.Base → Weight)
    (hphase : ∀ᵐ x ∂ProductModel.baseMeasure, ∀ k : ℤ,
      w x k = (AddCircle.toCircle (x i + k • (θ i : Invariant233.Circle)) : ℂ))
    (hm : NullMeasurable
      (fun x => A x (lp.single 2 (0 : ℤ) (1 : ℂ)) 0) ProductModel.baseMeasure)
    (hD : ∀ᵐ x ∂ProductModel.baseMeasure, Commute (A x) (diagonal (w x)))
    (hS : ∀ᵐ x ∂ProductModel.baseMeasure, Commute (A x) S)
    (hcov : ∀ᵐ x ∂ProductModel.baseMeasure,
      S * A (ProductModel.rotation θ x) = A x * S) :
    ∃ c : ℂ, ∀ᵐ x ∂ProductModel.baseMeasure,
      A x = c • (1 : Hilbert →L[ℂ] Hilbert) := by
  exact ae_eq_scalar_of_commute_irrational_diagonal_shift
    ProductModel.baseMeasure (ProductModel.rotation θ)
    (ProductModel.rotation_ergodic hθ) A w (θ i)
    (Invariant233.IndependentRotation.irrational_coordinate hθ i)
    (fun x => x i) hphase hm hD hS hcov

end Invariant233.WeightedShift

end OAI
