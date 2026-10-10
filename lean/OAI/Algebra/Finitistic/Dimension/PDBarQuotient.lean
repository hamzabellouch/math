import OAI.Algebra.Finitistic.Dimension.PDTensorFunctor
import OAI.Algebra.Finitistic.Bar.Balanced

namespace OAI
noncomputable section
open CategoryTheory TensorProduct
open scoped TensorProduct
namespace LittleFinitistic.PDBarQuotient
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)

/-- D with the actual right A action through f. -/
def RightBase (_f : A →ₐ[k] D) := D
instance : Ring (RightBase f) := inferInstanceAs (Ring D)
instance : Algebra k (RightBase f) := inferInstanceAs (Algebra k D)
instance : Module Aᵐᵒᵖ (RightBase f) := Module.compHom D f.toRingHom.op

@[simp] theorem right_smul (a : A) (d : RightBase f) :
    MulOpposite.op a • d = (show RightBase f from (show D from d) * f a) := rfl

variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- Quotient map from the detector tensor to the actual left D-linear bar quotient. -/
def forward : BalancedTensor.Tensor k A (RightBase f) V →ₗ[k] DerivedBar.Balanced.tensor f V :=
  BalancedTensor.lift
    ((TensorProduct.mk k (RightBase f) V).compr₂
      ((DerivedBar.Balanced.quotient f V).restrictScalars k))
    (fun a d v => DerivedBar.Balanced.balanced f V d a v)

omit [IsScalarTower k A V] in
/-- Every D-linear balancing relation lies in the detector's k-linear relation
space; the proof retains all left D multiples, rather than assuming the quotients equal. -/
theorem relations_kill : (DerivedBar.Balanced.relations f V).restrictScalars k ≤
    (BalancedTensor.relations k A (RightBase f) V).mkQ.ker := by
  intro z hz
  change (BalancedTensor.relations k A (RightBase f) V).mkQ z = 0
  have h : ∀ d : D, (BalancedTensor.relations k A (RightBase f) V).mkQ (d • z) = 0 := by
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b,a,v,rfl⟩ := hx
      intro d
      rw [smul_sub, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      change (BalancedTensor.relations k A (RightBase f) V).mkQ
        ((d*(b*f a)) ⊗ₜ[k] v - (d*b) ⊗ₜ[k] (a • v)) = 0
      erw [← mul_assoc, map_sub]
      exact sub_eq_zero.mpr (BalancedTensor.balance (k := k) (M := RightBase f) a (d*b) v)
    | zero => intro d; rw [smul_zero]; exact map_zero _
    | add x y hx hy ihx ihy =>
      intro d
      rw [smul_add]
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) (ihx d) (ihy d)).trans (add_zero _))
    | smul c x hx ih => intro d; simpa [smul_smul] using ih (d*c)
  simpa only [one_smul] using h 1

def inverse : DerivedBar.Balanced.tensor f V →ₗ[k] BalancedTensor.Tensor k A (RightBase f) V :=
  ((DerivedBar.Balanced.relations f V).restrictScalars k).liftQ
    (BalancedTensor.relations k A (RightBase f) V).mkQ (relations_kill f V)

omit [IsScalarTower k A V] in
@[simp] theorem forward_mk (d : RightBase f) (v : V) :
    forward f V (BalancedTensor.mk k A (RightBase f) V d v) =
      DerivedBar.Balanced.quotient f V (d ⊗ₜ[k] v) := rfl

omit [IsScalarTower k A V] in
@[simp] theorem inverse_quotient (d : D) (v : V) :
    inverse f V (DerivedBar.Balanced.quotient f V (d ⊗ₜ[k] v)) =
      BalancedTensor.mk k A (RightBase f) V d v := rfl

/-- Canonical actual quotient equivalence, on representatives d tensor v. -/
def equiv : BalancedTensor.Tensor k A (RightBase f) V ≃ₗ[k] DerivedBar.Balanced.tensor f V :=
  LinearEquiv.ofLinearMap (forward f V) (inverse f V) (by
    apply ((DerivedBar.Balanced.relations f V).restrictScalars k).linearMap_qext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro d
    apply LinearMap.ext
    intro v
    rfl) (by
    apply BalancedTensor.ext
    intro base vector
    rfl)

variable {V} {W : Type u} [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
theorem natural (h : V →ₗ[A] W) :
    (forward f W).comp (PDTensor.mapRight (k := k) (RightBase f) h) =
      ((DerivedBar.Balanced.map f V W h).restrictScalars k).comp (forward f V) := by
  apply BalancedTensor.ext
  intro d v
  rfl

omit [IsScalarTower k A V] in
/-- Exterior D multiplication agrees on every tensor generator. -/
theorem left_action (d b : D) (v : V) :
    forward f V (BalancedTensor.mk k A (RightBase f) V (d*b) v) =
      d • forward f V (BalancedTensor.mk k A (RightBase f) V b v) := by
  change DerivedBar.Balanced.quotient f V ((d*b) ⊗ₜ[k] v) =
    d • DerivedBar.Balanced.quotient f V (b ⊗ₜ[k] v)
  rw [← LinearMap.map_smul, TensorProduct.smul_tmul']
  rfl
end LittleFinitistic.PDBarQuotient

end

end OAI
