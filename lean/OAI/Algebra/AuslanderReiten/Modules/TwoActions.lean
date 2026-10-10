import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Module
import Mathlib.Algebra.CharP.Two

namespace OAI

namespace ArExplicit

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

def twoActionMap (a b : k) : (V × V) →ₗ[k] (V × V) :=
  (a • LinearMap.fst k V V + LinearMap.snd k V V).prod
    (b • LinearMap.fst k V V + LinearMap.snd k V V)

@[simp] theorem twoActionMap_apply (a b : k) (x y : V) :
    twoActionMap a b (x, y) = (a • x + y, b • x + y) := rfl

private def twoActionInverse (a b : k) (p : V × V) : V × V :=
  let g := (a - b)⁻¹ • (p.1 - p.2)
  (g, p.1 - a • g)

private theorem twoActionInverse_left (a b : k) (hab : a ≠ b) (p : V × V) :
    twoActionInverse a b (twoActionMap a b p) = p := by
  rcases p with ⟨x, y⟩
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hsub : (a • x + y) - (b • x + y) = (a - b) • x := by module
  have hx : (a - b)⁻¹ • ((a • x + y) - (b • x + y)) = x := by
    rw [hsub, smul_smul, inv_mul_cancel₀ hd, one_smul]
  change (_, _) = (x, y)
  simp only [twoActionMap_apply, hx]
  congr 1
  module

private theorem twoActionInverse_right (a b : k) (hab : a ≠ b) (p : V × V) :
    twoActionMap a b (twoActionInverse a b p) = p := by
  rcases p with ⟨u, v⟩
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  let g : V := (a - b)⁻¹ • (u - v)
  have hg : (a - b) • g = u - v := by
    dsimp [g]
    rw [smul_smul, mul_inv_cancel₀ hd, one_smul]
  change (a • g + (u - a • g), b • g + (u - a • g)) = (u, v)
  apply Prod.ext
  · module
  · calc
      b • g + (u - a • g) = u - (a - b) • g := by module
      _ = v := by rw [hg]; module

def twoActionEquiv (a b : k) (hab : a ≠ b) : (V × V) ≃ₗ[k] (V × V) where
  toLinearMap := twoActionMap a b
  invFun := twoActionInverse a b
  left_inv := twoActionInverse_left a b hab
  right_inv := twoActionInverse_right a b hab

theorem twoActionMap_bijective (a b : k) (hab : a ≠ b) :
    Function.Bijective (twoActionMap a b : (V × V) → V × V) :=
  (twoActionEquiv a b hab).bijective

def degreeZeroMap : (V × V) →ₗ[k] V :=
  LinearMap.fst k V V + LinearMap.snd k V V

theorem degreeZeroMap_surjective :
    Function.Surjective (degreeZeroMap (k := k) : (V × V) → V) := by
  intro v
  exact ⟨(v, 0), add_zero v⟩

theorem degreeZeroMap_kernel [CharP k 2] (x y : V) :
    degreeZeroMap (k := k) (x, y) = 0 ↔ x = y := by
  change x + y = 0 ↔ x = y
  rw [add_eq_zero_iff_eq_neg]
  have hy : -y = y := by
    have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
    have : y + y = 0 := by rw [← two_smul k y, htwo, zero_smul]
    exact neg_eq_iff_add_eq_zero.mpr this
  rw [hy]

theorem twoActionMap_same_not_injective [Nontrivial V] (a : k) :
    ¬ Function.Injective (twoActionMap a a : (V × V) → V × V) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  intro hinj
  have h : twoActionMap a a (x, -(a • x)) = twoActionMap a a (0, 0) := by
    simp
  have he := congrArg Prod.fst (hinj h)
  exact hx he

end ArExplicit

end OAI
