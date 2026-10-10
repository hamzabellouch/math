import OAI.Algebra.AuslanderReiten.Parameters
import Mathlib.LinearAlgebra.Prod

namespace OAI

noncomputable section
namespace ArExplicit
universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

def twoTwistLinear (a b : k) : (V × V) →ₗ[k] V × V where
  toFun x := (a • x.1 + x.2, b • x.1 + x.2)
  map_add' x y := by ext <;> simp [smul_add] <;> abel
  map_smul' r x := by ext <;> simp [smul_add, smul_comm a r, smul_comm b r]

theorem twoTwistLinear_injective (a b : k) (hab : a ≠ b) :
    Function.Injective (twoTwistLinear (V := V) a b) := by
  rintro ⟨x,y⟩ ⟨x',y'⟩ h
  have h₁ : a • x + y = a • x' + y' := congrArg Prod.fst h
  have h₂ : b • x + y = b • x' + y' := congrArg Prod.snd h
  have he : (a-b) • x = (a-b) • x' := by
    rw [sub_smul, sub_smul]
    have ht := congrArg₂ (fun s t : V => s-t) h₁ h₂
    simpa only [add_sub_add_right_eq_sub] using ht
  have hx : x = x' := by
    have ht := congrArg (fun z : V => (a-b)⁻¹ • z) he
    simpa only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hab), one_smul] using ht
  subst x'
  exact Prod.ext rfl (add_left_cancel h₁)

theorem twoTwistLinear_surjective (a b : k) (hab : a ≠ b) :
    Function.Surjective (twoTwistLinear (V := V) a b) := by
  rintro ⟨u,v⟩
  let x := (a-b)⁻¹ • (u-v)
  refine ⟨(x,u-a • x), Prod.ext ?_ ?_⟩
  · change a • x + (u-a • x) = u
    abel
  · have hx : (a-b) • x = u-v := by
      simp only [x, smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hab), one_smul]
    rw [sub_smul] at hx
    change b • x + (u-a • x) = v
    calc
      b • x + (u-a • x) = u-(a • x-b • x) := by abel
      _ = u-(u-v) := by rw [hx]
      _ = v := by abel

def twoTwistEquiv (a b : k) (hab : a ≠ b) : (V × V) ≃ₗ[k] V × V :=
  LinearEquiv.ofBijective (twoTwistLinear a b)
    ⟨twoTwistLinear_injective a b hab, twoTwistLinear_surjective a b hab⟩

def diagonalSubmodule : Submodule k (V × V) where
  carrier := {x | x.1 = x.2}
  zero_mem' := rfl
  add_mem' hx hy := congrArg₂ (· + ·) hx hy
  smul_mem' a _ hx := congrArg (a • ·) hx

def degreeZeroComparison : (V × V) →ₗ[k] diagonalSubmodule (k := k) (V := V) :=
  (twoTwistLinear 1 1).codRestrict _ (fun _ => rfl)

theorem degreeZeroComparison_surjective :
    Function.Surjective (degreeZeroComparison (k := k) (V := V)) := by
  rintro ⟨⟨x,y⟩,h⟩
  refine ⟨(0,x), Subtype.ext ?_⟩
  change (1 • (0 : V)+x,1 • (0 : V)+x) = (x,y)
  simpa only [smul_zero, zero_add] using (Prod.ext (rfl : x = x) (show x = y from h))

theorem degreeZeroComparison_nonzero_kernel (x : V) (hx : x ≠ 0) :
    (x,-x) ≠ (0,0) ∧ degreeZeroComparison (k := k) (x,-x) = 0 := by
  constructor
  · intro h
    exact hx (congrArg Prod.fst h)
  · apply Subtype.ext
    change (1 • x + -x,1 • x + -x) = (0,0)
    simp

end ArExplicit

end

end OAI
