import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorMap

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor
universe u
variable {k R F F' M M' : Type u} [CommRing k] [Ring R]
  [AddCommGroup F] [AddCommGroup F'] [AddCommGroup M] [AddCommGroup M']
  [Module k F] [Module k F'] [Module k M] [Module k M']
  [Module Rᵐᵒᵖ F] [Module Rᵐᵒᵖ F'] [Module R M] [Module R M']
variable (e : F ≃ₗ[k] F') (v : M ≃ₗ[k] M')
  (he : ∀ (r : Rᵐᵒᵖ) x, e (r • x) = r • e x)
  (hv : ∀ (r : R) x, v (r • x) = r • v x)

include he hv

omit hv in
theorem inverse_equivariant_right (r : Rᵐᵒᵖ) (x : F') :
    e.symm (r • x) = r • e.symm x := by
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

omit he in
theorem inverse_equivariant_left (r : R) (x : M') :
    v.symm (r • x) = r • v.symm x := by
  apply v.injective
  rw [LinearEquiv.apply_symm_apply, hv, LinearEquiv.apply_symm_apply]

def congr : BalancedTensor k R F M ≃ₗ[k] BalancedTensor k R F' M' where
  __ := map e.toLinearMap v.toLinearMap he hv
  invFun := map e.symm.toLinearMap v.symm.toLinearMap
    (inverse_equivariant_right e he) (inverse_equivariant_left v hv)
  left_inv z := by
    change map e.symm.toLinearMap v.symm.toLinearMap
      (inverse_equivariant_right e he) (inverse_equivariant_left v hv)
      (map e.toLinearMap v.toLinearMap he hv z) = z
    induction z using induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul f m => simp only [map_tmul, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
  right_inv z := by
    change map e.toLinearMap v.toLinearMap he hv
      (map e.symm.toLinearMap v.symm.toLinearMap
        (inverse_equivariant_right e he) (inverse_equivariant_left v hv) z) = z
    induction z using induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul f m => simp only [map_tmul, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]

@[simp] theorem congr_tmul (f : F) (m : M) :
    congr e v he hv (tmul f m) = tmul (e f) (v m) := rfl

variable {S : Type u} [Ring S] [Module S F] [Module S F']
  [SMulCommClass k S F] [SMulCommClass k S F']
  [SMulCommClass S Rᵐᵒᵖ F] [SMulCommClass S Rᵐᵒᵖ F']
  (hs : ∀ (s : S) x, e (s • x) = s • e x)

include hs

theorem congr_smul (s : S) (z : BalancedTensor k R F M) :
    congr e v he hv (s • z) = s • congr e v he hv z := by
  induction z using induction_on with
  | zero => simp
  | add z w hz hw => simp only [smul_add, map_add, hz, hw]
  | tmul f m => rw [smul_tmul, congr_tmul, hs, congr_tmul, smul_tmul]

def congrLeft : BalancedTensor k R F M ≃ₗ[S] BalancedTensor k R F' M' where
  __ := (congr e v he hv).toAddEquiv
  map_smul' := congr_smul e v he hv hs

end ArExplicit.BalancedTensor

end

end OAI
