import OAI.GroupTheory.PolycyclicRecognition.Algebra.InnerCentralizerMembership
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleMovingAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NonabelianFactorSystem

namespace OAI

/-! # Restriction of a factor system to the inner centralizer

Commutation of every quotient action with S forces every section factor into
the inner centralizer. The restriction retains the exact nonabelian cocycle.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] polynomialSubalgebraGroup
variable {L Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L] [Group Q]

theorem factor_mem_innerCentralizer (F : NonabelianFactorSystem L Q)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hact : ∀ q x, F.action q x = A q x)
    (S : L ≃ₗ⁅ℝ⁆ L) (hSA : ∀ q, Commute S.toLinearMap (A q).toLinearMap) (q r : Q) :
    F.factor q r ∈ innerCentralizerLieSubalgebra S := by
  have he : (A q).toLinearMap * (A r).toLinearMap =
      (polynomialInnerLieEquiv (F.factor q r)).toLinearMap * (A (q * r)).toLinearMap := by
    apply LinearMap.ext
    intro x
    change A q (A r x) = polynomialInnerLieEquiv (F.factor q r) (A (q * r) x)
    rw [polynomialInnerLieEquiv_apply, ← hact, ← hact, ← hact, F.action_mul_apply]
  apply (mem_innerCentralizerLieSubalgebra_iff S _).mpr
  have hc := (hSA q).mul_right (hSA r)
  rw [he] at hc
  exact linear_commute_of_mul_equiv_right S.toLinearMap
    (polynomialInnerLieEquiv (F.factor q r)).toLinearMap (A (q * r)).toLinearEquiv (hSA _) hc

def innerCentralizerFactorSystem (F : NonabelianFactorSystem L Q)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hact : ∀ q x, F.action q x = A q x)
    (S : L ≃ₗ⁅ℝ⁆ L) (hSA : ∀ q, Commute S.toLinearMap (A q).toLinearMap) :
    NonabelianFactorSystem (innerCentralizerLieSubalgebra S) Q where
  action q := innerCentralizerGroupAction S (A q) (hSA q)
  factor q r := ⟨F.factor q r, factor_mem_innerCentralizer F A hact S hSA q r⟩
  action_one := by
    apply DFunLike.ext
    intro x
    apply Subtype.ext
    change A 1 x = x
    rw [← hact, F.action_one]
    rfl
  factor_one_left q := Subtype.ext (F.factor_one_left q)
  factor_one_right q := Subtype.ext (F.factor_one_right q)
  action_mul q r := by
    apply DFunLike.ext
    intro x
    apply Subtype.ext
    change A q (A r x) = F.factor q r * A (q * r) x * (F.factor q r)⁻¹
    rw [← hact, ← hact, ← hact, F.action_mul_apply]
  cocycle q r s := by
    apply Subtype.ext
    change F.factor q r * F.factor (q * r) s = A q (F.factor r s) * F.factor q (r * s)
    rw [← hact]
    exact F.cocycle q r s

end PolycyclicRecognition

end

end OAI
