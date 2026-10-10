import OAI.GroupTheory.PolycyclicRecognition.Algebra.NonabelianFactorSystem

namespace OAI

/-! # Removing a commuting quotient action from a factor system

The original cocycle is retained. Fixedness of its values is exactly the
condition needed to remove the commuting semisimple quotient action.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {N Q : Type} [Group N] [Group Q] [IsMulCommutative Q]
  (R : NonabelianFactorSystem N Q) (χ : Q →* MulAut N)
  (hcomm : ∀ q r, Commute (R.action q) (χ r))
  (hfix : ∀ q r s, χ q (R.factor r s) = R.factor r s)

include hfix in
omit [IsMulCommutative Q] in
private theorem twist_inverse_fixed (q r s : Q) :
    (χ q)⁻¹ (R.factor r s) = R.factor r s := by
  apply (χ q).injective
  change χ q ((χ q).symm (R.factor r s)) = χ q (R.factor r s)
  rw [MulEquiv.apply_symm_apply, hfix]

private theorem twist_inverse_product (q r : Q) (x : N) :
    (χ q)⁻¹ ((χ r)⁻¹ x) = (χ (q * r))⁻¹ x := by
  change ((χ q)⁻¹ * (χ r)⁻¹) x = (χ (q * r))⁻¹ x
  rw [mul_comm q r, map_mul, mul_inv_rev]

include hcomm in
omit [IsMulCommutative Q] in
private theorem twist_inverse_commute (q r : Q) (x : N) :
    R.action q ((χ r)⁻¹ x) = (χ r)⁻¹ (R.action q x) :=
  DFunLike.congr_fun (hcomm q r).inv_right.eq x

include hcomm hfix in
/-- Remove the actual quotient homomorphism from every section action. -/
def NonabelianFactorSystem.twist : NonabelianFactorSystem N Q where
  action q := (χ q)⁻¹ * R.action q
  factor := R.factor
  action_one := by rw [map_one, inv_one, one_mul, R.action_one]
  factor_one_left := R.factor_one_left
  factor_one_right := R.factor_one_right
  action_mul q r := by
    apply DFunLike.ext
    intro x
    change (χ q)⁻¹ (R.action q ((χ r)⁻¹ (R.action r x))) =
      R.factor q r * (χ (q * r))⁻¹ (R.action (q * r) x) * (R.factor q r)⁻¹
    rw [twist_inverse_commute R χ hcomm, twist_inverse_product,
      R.action_mul_apply, map_mul, map_mul, map_inv,
      twist_inverse_fixed R χ hfix]
  cocycle q r s := by
    change R.factor q r * R.factor (q * r) s =
      (χ q)⁻¹ (R.action q (R.factor r s)) * R.factor q (r * s)
    rw [← twist_inverse_commute R χ hcomm,
      twist_inverse_fixed R χ hfix, R.cocycle]

theorem factorSystem_twist_recompose (q : Q) (x : N) :
    (R.twist χ hcomm hfix).action q (χ q x) = R.action q x := by
  change (χ q)⁻¹ (R.action q (χ q x)) = R.action q x
  have hc : R.action q (χ q x) = χ q (R.action q x) :=
    DFunLike.congr_fun (hcomm q q).eq x
  rw [hc]
  exact (χ q).symm_apply_apply _

end PolycyclicRecognition

end

end OAI
