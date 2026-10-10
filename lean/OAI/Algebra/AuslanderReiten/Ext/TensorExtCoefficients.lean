import OAI.Algebra.AuslanderReiten.Ext.ExtKunneth
import Mathlib.LinearAlgebra.Pi

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (X U : ModuleCat.{u} A) (Y V : ModuleCat.{u} B)

abbrev extCoefficients (n : ℕ) :=
  ∀ d : Diagonal n, Ext X U d.val.1 ⊗[k] Ext Y V d.val.2

abbrev diagonalFirst (n : ℕ) (d : Diagonal n) : Diagonal (n+3) :=
  ⟨(d.val.1+3,d.val.2), by have := d.property; omega⟩

abbrev diagonalSecond (n : ℕ) (d : Diagonal n) : Diagonal (n+3) :=
  ⟨(d.val.1,d.val.2+3), by have := d.property; omega⟩

variable (a : Ext X X 3) (b : Ext Y Y 3)

def coefficientFirst (n : ℕ) : extCoefficients k A B X U Y V n →ₗ[k]
    extCoefficients k A B X U Y V (n+3) := by
  classical
  exact ∑ d : Diagonal n,
    (LinearMap.single k (fun e : Diagonal (n+3) => Ext X U e.val.1 ⊗[k] Ext Y V e.val.2)
      (diagonalFirst n d)).comp
      ((TensorProduct.map (Ext.bilinearCompOfLinear k X X U 3 d.val.1 (d.val.1+3) (by omega) a)
        (LinearMap.id : Ext Y V d.val.2 →ₗ[k] Ext Y V d.val.2)).comp (LinearMap.proj d))

def coefficientSecond (n : ℕ) : extCoefficients k A B X U Y V n →ₗ[k]
    extCoefficients k A B X U Y V (n+3) := by
  classical
  exact ∑ d : Diagonal n,
    (LinearMap.single k (fun e : Diagonal (n+3) => Ext X U e.val.1 ⊗[k] Ext Y V e.val.2)
      (diagonalSecond n d)).comp
      ((TensorProduct.map (LinearMap.id : Ext X U d.val.1 →ₗ[k] Ext X U d.val.1)
        (Ext.bilinearCompOfLinear k Y Y V 3 d.val.2 (d.val.2+3) (by omega) b)).comp (LinearMap.proj d))

theorem coefficientFirst_single (n : ℕ) (d : Diagonal n)
    (x : Ext X U d.val.1) (y : Ext Y V d.val.2) :
    coefficientFirst k A B X U Y V a n (Pi.single d (x ⊗ₜ[k] y)) =
      Pi.single (diagonalFirst n d) (a.comp x (by change 3+d.val.1=d.val.1+3; omega) ⊗ₜ[k] y) := by
  classical
  simp only [coefficientFirst, diagonalFirst, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single d]
  · simp only [Pi.single_eq_same, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.single_apply]
    rfl
  · intro e he hne
    rw [Pi.single_eq_of_ne hne, map_zero, map_zero]
  · simp

theorem coefficientSecond_single (n : ℕ) (d : Diagonal n)
    (x : Ext X U d.val.1) (y : Ext Y V d.val.2) :
    coefficientSecond k A B X U Y V b n (Pi.single d (x ⊗ₜ[k] y)) =
      Pi.single (diagonalSecond n d) (x ⊗ₜ[k] b.comp y (by change 3+d.val.2=d.val.2+3; omega)) := by
  classical
  simp only [coefficientSecond, diagonalSecond, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single d]
  · simp only [Pi.single_eq_same, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.single_apply]
    rfl
  · intro e he hne
    rw [Pi.single_eq_of_ne hne, map_zero, map_zero]
  · simp

end ArExplicit.ExternalTensor

end

end OAI
