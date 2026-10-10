import OAI.Analysis.IrrationalRotation.Model.ProductBase
import OAI.Analysis.IrrationalRotation.Product.ProductErgodicity

namespace OAI

namespace Invariant233.ProductModel

open MeasureTheory

theorem measurePreserving_rotationIterate (θ : ℕ → ℝ) (k : ℤ) :
    MeasurePreserving (rotationIterate θ k) baseMeasure baseMeasure :=
  InvariantProjection.ProductRotation.measurePreserving_product_translation
    (fun i => (((k : ℝ) * θ i : ℝ) : UnitAddCircle))

theorem measurePreserving_rotation (θ : ℕ → ℝ) :
    MeasurePreserving (rotation θ) baseMeasure baseMeasure :=
  InvariantProjection.ProductRotation.measurePreserving_product_translation
    (fun i => (θ i : UnitAddCircle))

theorem rotationIterate_ergodic {θ : ℕ → ℝ}
    (hθ : JointlyRationallyIndependent θ) {k : ℤ} (hk : k ≠ 0) :
    Ergodic (rotationIterate θ k) baseMeasure :=
  InvariantProjection.ProductRotation.product_rotation_integer_ergodic hθ hk

theorem rotation_ergodic {θ : ℕ → ℝ}
    (hθ : JointlyRationallyIndependent θ) :
    Ergodic (rotation θ) baseMeasure :=
  InvariantProjection.ProductRotation.product_rotation_ergodic hθ

theorem rotation_totalErgodic {θ : ℕ → ℝ}
    (hθ : JointlyRationallyIndependent θ) {n : ℕ} (hn : 0 < n) :
    Ergodic (rotation θ)^[n] baseMeasure :=
  InvariantProjection.ProductRotation.product_rotation_totalErgodic hθ hn

theorem rotationIterate_ne_self {θ : ℕ → ℝ}
    (hθ : JointlyRationallyIndependent θ) {k : ℤ} (hk : k ≠ 0) (x : Base) :
    rotationIterate θ k x ≠ x :=
  InvariantProjection.ProductRotation.product_rotation_free θ
    (InvariantProjection.ProductRotation.integer_affine_independent hθ) hk x

end Invariant233.ProductModel

end OAI
