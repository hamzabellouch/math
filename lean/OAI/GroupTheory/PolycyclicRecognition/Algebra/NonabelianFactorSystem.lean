import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Tactic.Group

namespace OAI

/-! # Groups from a normalized nonabelian factor system

The multiplication retains the inner correction, so quotient lifts are not
required to commute or to give a splitting.
-/

namespace PolycyclicRecognition

structure NonabelianFactorSystem (N Q : Type*) [Group N] [Group Q] where
  action : Q → MulAut N
  factor : Q → Q → N
  action_one : action 1 = 1
  factor_one_left : ∀ q, factor 1 q = 1
  factor_one_right : ∀ q, factor q 1 = 1
  action_mul : ∀ q r, action q * action r = MulAut.conj (factor q r) * action (q * r)
  cocycle : ∀ q r s, factor q r * factor (q * r) s =
    action q (factor r s) * factor q (r * s)

namespace NonabelianFactorSystem
variable {N Q : Type*} [Group N] [Group Q] (S : NonabelianFactorSystem N Q)

theorem action_mul_apply (q r : Q) (x : N) :
    S.action q (S.action r x) =
      S.factor q r * S.action (q * r) x * (S.factor q r)⁻¹ :=
  DFunLike.congr_fun (S.action_mul q r) x

end NonabelianFactorSystem

@[ext] structure FactorExtension {N Q : Type*} [Group N] [Group Q]
    (S : NonabelianFactorSystem N Q) where
  left : N
  right : Q

namespace FactorExtension
variable {N Q : Type*} [Group N] [Group Q] (S : NonabelianFactorSystem N Q)

instance : One (FactorExtension S) := ⟨⟨1, 1⟩⟩
instance : Mul (FactorExtension S) :=
  ⟨fun a b => ⟨a.left * S.action a.right b.left * S.factor a.right b.right,
    a.right * b.right⟩⟩
instance : Inv (FactorExtension S) :=
  ⟨fun a => ⟨(S.factor a.right⁻¹ a.right)⁻¹ * S.action a.right⁻¹ a.left⁻¹, a.right⁻¹⟩⟩

@[simp] theorem one_left : (1 : FactorExtension S).left = 1 := rfl
@[simp] theorem one_right : (1 : FactorExtension S).right = 1 := rfl
@[simp] theorem mul_left (a b : FactorExtension S) :
    (a * b).left = a.left * S.action a.right b.left * S.factor a.right b.right := rfl
@[simp] theorem mul_right (a b : FactorExtension S) : (a * b).right = a.right * b.right := rfl
@[simp] theorem inv_left (a : FactorExtension S) :
    a⁻¹.left = (S.factor a.right⁻¹ a.right)⁻¹ * S.action a.right⁻¹ a.left⁻¹ := rfl
@[simp] theorem inv_right (a : FactorExtension S) : a⁻¹.right = a.right⁻¹ := rfl

instance : Group (FactorExtension S) where
  mul_assoc a b c := by
    apply FactorExtension.ext
    · simp only [mul_left, mul_right, map_mul, S.action_mul_apply]
      simp only [mul_assoc]
      rw [← S.cocycle]
      group
    · exact mul_assoc _ _ _
  one_mul a := by
    apply FactorExtension.ext
    · simp only [mul_left, one_left, one_right, S.action_one, MulAut.one_apply,
        S.factor_one_left, one_mul, mul_one]
    · exact one_mul _
  mul_one a := by
    apply FactorExtension.ext
    · simp only [mul_left, one_left, one_right, map_one, S.factor_one_right, mul_one]
    · exact mul_one _
  inv_mul_cancel a := by
    apply FactorExtension.ext
    · simp only [mul_left, inv_left, inv_right, map_inv, one_left]
      group
    · exact inv_mul_cancel _

/-- The kernel inclusion into the group with the given factor system. -/
def inl : N →* FactorExtension S where
  toFun x := ⟨x, 1⟩
  map_one' := rfl
  map_mul' x y := by
    apply FactorExtension.ext
    · simp only [mul_left, S.action_one, MulAut.one_apply, S.factor_one_left, mul_one]
    · exact (one_mul (1 : Q)).symm

/-- Projection to the original quotient. -/
def projection : FactorExtension S →* Q where
  toFun a := a.right
  map_one' := rfl
  map_mul' _ _ := rfl

theorem inl_injective : Function.Injective (inl S) := by
  intro x y h
  exact congrArg FactorExtension.left h

theorem projection_surjective : Function.Surjective (projection S) :=
  fun q => ⟨⟨1, q⟩, rfl⟩

/-- The product coordinates are an actual equivalence of sets. -/
def equivProd : FactorExtension S ≃ N × Q where
  toFun a := (a.left, a.right)
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end FactorExtension
end PolycyclicRecognition

end OAI
