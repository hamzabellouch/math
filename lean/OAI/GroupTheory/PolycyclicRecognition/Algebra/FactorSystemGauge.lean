import OAI.GroupTheory.PolycyclicRecognition.Algebra.NonabelianFactorSystem

namespace OAI

/-! # Changing quotient lifts by an explicit kernel element

This permits inner corrections in the completed kernel without changing the
extension. The correction need not belong to the original lattice.
-/

namespace PolycyclicRecognition.NonabelianFactorSystem
variable {N Q : Type*} [Group N] [Group Q]
  (S : NonabelianFactorSystem N Q) (b : Q → N) (hb : b 1 = 1)

def gauge : NonabelianFactorSystem N Q where
  action q := MulAut.conj (b q) * S.action q
  factor q r := b q * S.action q (b r) * S.factor q r * (b (q * r))⁻¹
  action_one := by simp only [hb, S.action_one, map_one, mul_one]
  factor_one_left q := by
    simp only [hb, S.action_one, MulAut.one_apply, S.factor_one_left,
      one_mul, mul_one, mul_inv_cancel]
  factor_one_right q := by
    simp only [hb, map_one, S.factor_one_right, mul_one, mul_inv_cancel]
  action_mul q r := by
    apply DFunLike.ext
    intro x
    change b q * S.action q (b r * S.action r x * (b r)⁻¹) * (b q)⁻¹ =
      (b q * S.action q (b r) * S.factor q r * (b (q * r))⁻¹) *
        (b (q * r) * S.action (q * r) x * (b (q * r))⁻¹) *
          (b q * S.action q (b r) * S.factor q r * (b (q * r))⁻¹)⁻¹
    simp only [map_mul, map_inv, S.action_mul_apply]
    group
  cocycle q r s := by
    change (b q * S.action q (b r) * S.factor q r * (b (q * r))⁻¹) *
        (b (q * r) * S.action (q * r) (b s) * S.factor (q * r) s * (b ((q * r) * s))⁻¹) =
      (b q * S.action q (b r * S.action r (b s) * S.factor r s * (b (r * s))⁻¹) * (b q)⁻¹) *
        (b q * S.action q (b (r * s)) * S.factor q (r * s) * (b (q * (r * s)))⁻¹)
    simp only [map_mul, map_inv, S.action_mul_apply]
    have hc : S.action q (S.factor r s) =
        S.factor q r * S.factor (q * r) s * (S.factor q (r * s))⁻¹ :=
      eq_mul_inv_iff_mul_eq.mpr (S.cocycle q r s).symm
    rw [hc, mul_assoc q r s]
    group

/-- Right multiplication by the lift correction is an exact group isomorphism. -/
def gaugeEquiv : FactorExtension (S.gauge b hb) ≃* FactorExtension S where
  toFun a := ⟨a.left * b a.right, a.right⟩
  invFun a := ⟨a.left * (b a.right)⁻¹, a.right⟩
  left_inv a := by apply FactorExtension.ext; exact mul_inv_cancel_right _ _; rfl
  right_inv a := by apply FactorExtension.ext; exact inv_mul_cancel_right _ _; rfl
  map_mul' a c := by
    apply FactorExtension.ext
    · change (a.left * (b a.right * S.action a.right c.left * (b a.right)⁻¹) *
          (b a.right * S.action a.right (b c.right) * S.factor a.right c.right *
            (b (a.right * c.right))⁻¹)) * b (a.right * c.right) =
        (a.left * b a.right) * S.action a.right (c.left * b c.right) * S.factor a.right c.right
      rw [map_mul]
      group
    · rfl

end PolycyclicRecognition.NonabelianFactorSystem

end OAI
