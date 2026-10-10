import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Abel

namespace OAI

/-! # The group defined by a bilinear central cocycle

These coordinate groups provide the two-step case of the nilpotent lattice
construction. Integral and real coefficients use exactly the same law.
-/

namespace PolycyclicRecognition
variable {R V W : Type*} [CommRing R] [AddCommGroup V] [AddCommGroup W]
  [Module R V] [Module R W]

def BilinearCentralGroup (_B : V →ₗ[R] V →ₗ[R] W) := V × W

namespace BilinearCentralGroup
variable (B : V →ₗ[R] V →ₗ[R] W)

instance : Group (BilinearCentralGroup B) where
  mul x y := (x.1 + y.1, x.2 + y.2 + B x.1 y.1)
  one := (0, 0)
  inv x := (-x.1, -x.2 + B x.1 x.1)
  mul_assoc x y z := by
    apply Prod.ext
    · exact add_assoc _ _ _
    · change (x.2 + y.2 + B x.1 y.1) + z.2 + B (x.1 + y.1) z.1 =
        x.2 + (y.2 + z.2 + B y.1 z.1) + B x.1 (y.1 + z.1)
      simp only [map_add, LinearMap.add_apply]
      abel
  one_mul x := by
    change (0 + x.1, 0 + x.2 + B 0 x.1) = x
    apply Prod.ext <;> simp
  mul_one x := by
    change (x.1 + 0, x.2 + 0 + B x.1 0) = x
    apply Prod.ext <;> simp
  inv_mul_cancel x := by
    apply Prod.ext
    · exact neg_add_cancel _
    · change (-x.2 + B x.1 x.1) + x.2 + B (-x.1) x.1 = 0
      simp only [map_neg, LinearMap.neg_apply]
      abel

@[simp] theorem mul_fst (x y : BilinearCentralGroup B) : (x * y).1 = x.1 + y.1 := rfl
@[simp] theorem mul_snd (x y : BilinearCentralGroup B) :
    (x * y).2 = x.2 + y.2 + B x.1 y.1 := rfl
@[simp] theorem one_fst : (1 : BilinearCentralGroup B).1 = 0 := rfl
@[simp] theorem one_snd : (1 : BilinearCentralGroup B).2 = 0 := rfl

def projection : BilinearCentralGroup B →* Multiplicative V where
  toFun x := Multiplicative.ofAdd x.1
  map_one' := rfl
  map_mul' _ _ := rfl

theorem projection_ker_le_center : (projection B).ker ≤ Subgroup.center (BilinearCentralGroup B) := by
  intro x hx
  have hx0 : x.1 = 0 := congrArg Multiplicative.toAdd hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Prod.ext
  · simp only [mul_fst, hx0, add_zero, zero_add]
  · simp only [mul_snd, hx0, map_zero, LinearMap.zero_apply, add_zero]
    exact add_comm _ _

instance : Group.IsNilpotent (BilinearCentralGroup B) :=
  Subgroup.isNilpotent_of_ker_le_center (projection B) (projection_ker_le_center B)

def map {V' W' : Type*} [AddCommGroup V'] [AddCommGroup W'] [Module R V'] [Module R W']
    (B' : V' →ₗ[R] V' →ₗ[R] W') (f : V →+ V') (g : W →+ W')
    (hB : ∀ x y, g (B x y) = B' (f x) (f y)) :
    BilinearCentralGroup B →* BilinearCentralGroup B' where
  toFun x := (f x.1, g x.2)
  map_one' := by apply Prod.ext <;> exact map_zero _
  map_mul' x y := by
    apply Prod.ext
    · exact map_add f _ _
    · change g (x.2 + y.2 + B x.1 y.1) = g x.2 + g y.2 + B' (f x.1) (f y.1)
      rw [map_add, map_add, hB]

theorem map_injective {V' W' : Type*} [AddCommGroup V'] [AddCommGroup W']
    [Module R V'] [Module R W'] (B' : V' →ₗ[R] V' →ₗ[R] W')
    (f : V →+ V') (g : W →+ W') (hB : ∀ x y, g (B x y) = B' (f x) (f y))
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (map B B' f g hB) := by
  intro x y h
  exact Prod.ext (hf (congrArg Prod.fst h)) (hg (congrArg Prod.snd h))

end BilinearCentralGroup
end PolycyclicRecognition

end OAI
