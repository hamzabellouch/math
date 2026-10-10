import OAI.Algebra.AuslanderReiten.Bar.TBarLift
import OAI.Algebra.AuslanderReiten.Cocycles.TwistedBoundary
import OAI.Algebra.AuslanderReiten.Modules.TwistedOneCochain

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q

def Z (H : kˣ) :
    AbsoluteBar.twistedObject k R (TrivialExtension.twist H) 2 →ₗ[AbsoluteBar.Enveloping k R]
      AbsoluteBar.moduleObject k R 0 :=
  AbsoluteBar.oneCochain k R (TrivialExtension.twist H) (CocycleData.z q H)

private theorem twist_symm_apply (H : kˣ) (a : R) :
    (TrivialExtension.twist H).symm a = TrivialExtension.twist H⁻¹ a := rfl

private theorem casimirMap_right (H : kˣ) (a : R) :
    AbsoluteBar.casimirMap k R (twistedCasimir q H) a =
      AbsoluteBar.right k R 1 (MulOpposite.op ((TrivialExtension.twist H).symm a))
        (twistedCasimir q H) := by
  have hh := twistedCasimir_equivariant q H ((TrivialExtension.twist H).symm a)
  rw [AlgEquiv.apply_symm_apply] at hh
  exact hh

theorem pB_bottom_tmul (H : kˣ) (a b c d : R) :
    AbsoluteBar.cochain3Linear k R (CocycleData.p q)
      (AbsoluteBar.casimirInsertion k R (twistedCasimir q H) 3
        (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] d)))) =
      a * (∑ i : TIndex, CocycleData.p q b c (TrivialExtension.twist H (vector q i)) *
        vector q i.star) * (TrivialExtension.twist H).symm d := by
  change AbsoluteBar.cochain3Linear k R (CocycleData.p q)
    (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] AbsoluteBar.casimirMap k R (twistedCasimir q H) d))) = _
  rw [casimirMap_right]
  simp only [twistedCasimir, map_sum, AbsoluteBar.right_tmul k R 0,
    AbsoluteBar.right_zero k R, MulOpposite.unop_op,
    TensorProduct.tmul_sum, AbsoluteBar.cochain3Linear_tmul k R (CocycleData.p q)]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc]

variable [CharP k 2]

theorem pB_bottom_linear (H : kˣ) :
    (AbsoluteBar.cochain3Linear k R (CocycleData.p q)).comp
        (AbsoluteBar.casimirInsertion k R (twistedCasimir q H) 3) =
      (AbsoluteBar.oneCochainLinear k R (TrivialExtension.twist H) (CocycleData.z q H)).comp
        (AbsoluteBar.boundary k R 2) := by
  apply TensorProduct.ext'
  intro a x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul b x =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul c d =>
      change AbsoluteBar.cochain3Linear k R (CocycleData.p q)
          (AbsoluteBar.casimirInsertion k R (twistedCasimir q H) 3
            (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] d)))) =
        AbsoluteBar.oneCochainLinear k R (TrivialExtension.twist H) (CocycleData.z q H)
          (AbsoluteBar.boundary k R 2 (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] d))))
      rw [pB_bottom_tmul, AbsoluteBar.oneCochain_boundary_tmul]
      rw [CocycleData.twisted_boundary]
      rfl

theorem pB_bottom (H : kˣ) :
    (AbsoluteBar.cochain3 k R (CocycleData.p q)).comp (B q H 3) =
      (Z q H).comp (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) 2) := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (pB_bottom_linear q H) x

end ArExplicit.T

end

end OAI
