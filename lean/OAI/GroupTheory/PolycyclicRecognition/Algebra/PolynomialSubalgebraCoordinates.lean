import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialSubalgebraGroup
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentIntrinsicIntegration
import Mathlib.Algebra.Group.Ext

namespace OAI

/-! # Smooth polynomial coordinates on an inherited nilpotent subgroup

Intrinsic integration identifies the independently constructed BCH law with
the ambient group's restricted law. This retains the actual embedded subgroup.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

@[instance_reducible] def normedLieSubalgebra (K : LieSubalgebra ℝ L) :
    RealNormedLieAlgebra K := by
  let : NormedAddCommGroup K := NormedAddCommGroup.induced K L K.incl Subtype.val_injective
  let : NormedSpace ℝ K := NormedSpace.induced ℝ K L K.incl.toLinearMap
  exact { (inferInstance : NormedAddCommGroup K), (inferInstance : LieRing K),
    (inferInstance : NormedSpace ℝ K), (inferInstance : LieAlgebra ℝ K) with }

/-- Any intrinsic polynomial model on a Lie subalgebra has the inherited product. -/
theorem polynomialSubalgebra_intrinsic_mul (K : LieSubalgebra ℝ L)
    (hnil : LieRing.IsNilpotent K) :
    letI := normedLieSubalgebra K
    ∀ Q : PolynomialExponentialCoordinates K, ∀ x y : K,
      (Q.group).mul x y = (polynomialSubalgebraGroup K).mul x y := by
  let := normedLieSubalgebra K
  intro Q x y
  let := Q
  let : Group K := Q.group
  obtain ⟨φ, _, hφ⟩ := integrate_polynomial_nilpotent
    (fun x : GroupLieAlgebra (𝓘(ℝ, L)) L => (x : L))
    PolynomialExponentialCoordinates.isGroupExponential_identity K hnil
    (P.tangentEquiv.toLieHom.comp K.incl)
  have hf (z : K) : φ z = (z : L) := by
    rw [hφ]
    exact P.tangentEquiv_apply z
  apply Subtype.ext
  change ((Q.group).mul x y : L) = (x : L) * (y : L)
  have hm := φ.map_mul x y
  rw [hf, hf, hf] at hm
  exact hm

theorem polynomialSubalgebra_intrinsic_group (K : LieSubalgebra ℝ L)
    (hnil : LieRing.IsNilpotent K) :
    letI := normedLieSubalgebra K
    ∀ Q : PolynomialExponentialCoordinates K, Q.group = polynomialSubalgebraGroup K := by
  let := normedLieSubalgebra K
  intro Q
  apply Group.ext
  funext x y
  exact polynomialSubalgebra_intrinsic_mul K hnil Q x y

/-- The inherited group itself admits polynomial exponential coordinates. -/
theorem polynomialSubalgebra_coordinates (K : LieSubalgebra ℝ L)
    (hnil : LieRing.IsNilpotent K) :
    letI := normedLieSubalgebra K
    ∃ Q : PolynomialExponentialCoordinates K, Q.group = polynomialSubalgebraGroup K := by
  let := normedLieSubalgebra K
  obtain ⟨Q⟩ := polynomialExponentialCoordinates_nilpotent K hnil
  exact ⟨Q, polynomialSubalgebra_intrinsic_group K hnil Q⟩

/-- The topology and inherited multiplication form the same smooth Lie group. -/
theorem polynomialSubalgebra_lieGroup (K : LieSubalgebra ℝ L)
    (hnil : LieRing.IsNilpotent K) :
    letI := normedLieSubalgebra K
    @LieGroup ℝ _ K _ K _ _ (𝓘(ℝ, K)) ⊤ K (polynomialSubalgebraGroup K) _
      (chartedSpaceSelf K) := by
  let := normedLieSubalgebra K
  obtain ⟨Q, hQ⟩ := polynomialSubalgebra_coordinates K hnil
  rw [← hQ]
  exact Q.lieGroup

end PolycyclicRecognition

end

end OAI
