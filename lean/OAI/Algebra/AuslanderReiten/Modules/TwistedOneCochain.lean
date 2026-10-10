import OAI.Algebra.AuslanderReiten.Bar.TwistedBar

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.AbsoluteBar

universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

def oneSuffix (h : R ≃ₐ[k] R) (z : R →ₗ[k] R) : object k R 1 →ₗ[k] R :=
  TensorProduct.lift (((LinearMap.mul k R).comp z).compl₂ h.symm.toLinearMap)

@[simp] theorem oneSuffix_tmul (h : R ≃ₐ[k] R) (z : R →ₗ[k] R) (b c : R) :
    oneSuffix k R h z (b ⊗ₜ[k] c) = z b * h.symm c := rfl

def oneCochainLinear (h : R ≃ₐ[k] R) (z : R →ₗ[k] R) : object k R 2 →ₗ[k] R :=
  TensorProduct.lift ((LinearMap.mul k R).compl₂ (oneSuffix k R h z))

@[simp] theorem oneCochainLinear_tmul (h : R ≃ₐ[k] R) (z : R →ₗ[k] R) (a b c : R) :
    oneCochainLinear k R h z (a ⊗ₜ[k] (b ⊗ₜ[k] c)) = a * z b * h.symm c := by
  exact (mul_assoc _ _ _).symm

theorem oneCochainLinear_left (h : R ≃ₐ[k] R) (z : R →ₗ[k] R) (a : R)
    (x : object k R 2) :
    oneCochainLinear k R h z (left k R 2 a x) = a * oneCochainLinear k R h z x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  | tmul b x => exact mul_assoc _ _ _

theorem oneCochainLinear_right (h : R ≃ₐ[k] R) (z : R →ₗ[k] R) (a : R)
    (x : object k R 2) :
    oneCochainLinear k R h z (right k R 2 (MulOpposite.op (h a)) x) =
      oneCochainLinear k R h z x * a := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, add_mul]
  | tmul b x =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      simp only [TensorProduct.tmul_add, map_add, hx, hy, add_mul]
    | tmul c d =>
      change b * (z c * h.symm (d * h a)) = b * (z c * h.symm d) * a
      rw [map_mul, h.symm_apply_apply]
      simp only [mul_assoc]

def oneCochain (h : R ≃ₐ[k] R) (z : R →ₗ[k] R) :
    twistedObject k R h 2 →ₗ[Enveloping k R] moduleObject k R 0 :=
  twistedToOrdinary k R h (oneCochainLinear k R h z)
    (oneCochainLinear_left k R h z) (oneCochainLinear_right k R h z)

theorem oneCochain_boundary_tmul (h : R ≃ₐ[k] R) (z : R →ₗ[k] R) (a b c d : R) :
    oneCochainLinear k R h z (boundary k R 2 (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] d)))) =
      a * (b * z c + z (b * c) + z b * h.symm c) * h.symm d := by
  simp only [boundary_succ_tmul k R 1, boundary_succ_tmul k R 0,
    boundary_zero_tmul k R, left_tmul k R 1, left_tmul k R 0,
    TensorProduct.tmul_add, map_add, oneCochainLinear_tmul k R h z,
    map_mul, mul_add, add_mul, mul_assoc, add_assoc]

end ArExplicit.AbsoluteBar

end

end OAI
