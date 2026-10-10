import OAI.Algebra.AuslanderReiten.Bar.ModuleBarCochain
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module k M]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)

def transport : (n : ℕ) → object k R M n ≃ₗ[k] object k R M n
  | 0 => e
  | n+1 => TensorProduct.congr h.toLinearEquiv (transport n)

@[simp] theorem transport_zero (m : M) : transport k R M h e 0 m = e m := rfl
@[simp] theorem transport_tmul (n : ℕ) (a : R) (x : object k R M n) :
    transport k R M h e (n+1) (a ⊗ₜ[k] x) = h a ⊗ₜ[k] transport k R M h e n x := rfl

variable [Module R M] [IsScalarTower k R M]
variable (he : ∀ a m, e (a • m) = h a • e m)
include he

theorem transport_left (n : ℕ) (a : R) (x : object k R M n) :
    transport k R M h e n (left k R M n a x) =
      left k R M n (h a) (transport k R M h e n x) := by
  cases n with
  | zero => exact he a x
  | succ n =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b x =>
      rw [left_tmul, transport_tmul, transport_tmul, left_tmul, map_mul]

theorem transport_boundary (n : ℕ) (x : object k R M (n+1)) :
    transport k R M h e n (boundary k R M n x) =
      boundary k R M n (transport k R M h e (n+1) x) := by
  induction n with
  | zero =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => exact he a x
  | succ n ih =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x =>
      rw [boundary_succ_tmul, map_add, transport_left k R M h e he,
        transport_tmul, transport_tmul, boundary_succ_tmul, ih]

def transportLinear (n : ℕ) : moduleObject k R M n →ₗ[R]
    (ModuleCat.restrictScalars h.toRingHom).obj (moduleObject k R M n) where
  toFun := transport k R M h e n
  map_add' := (transport k R M h e n).map_add
  map_smul' a x := transport_left k R M h e he n a x

def transportIso (n : ℕ) : moduleObject k R M n ≅
    (ModuleCat.restrictScalars h.toRingHom).obj (moduleObject k R M n) :=
  (LinearEquiv.ofBijective (transportLinear k R M h e he n)
    (transport k R M h e n).bijective).toModuleIso

@[simp] theorem transportIso_hom_apply (n : ℕ) (x : moduleObject k R M n) :
    (transportIso k R M h e he n).hom.hom x = transport k R M h e n x := rfl

variable [CharP k 2]

def transportComplexIso : complex k R M ≅
    ((ModuleCat.restrictScalars h.toRingHom).mapHomologicalComplex (.down ℕ)).obj
      (complex k R M) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => transportIso k R M h e he (n+1))
    (fun i j hij => by
      have hi : j+1 = i := hij
      subst i
      change (transportIso k R M h e he (j+2)).hom ≫
          (ModuleCat.restrictScalars h.toRingHom).map ((complex k R M).d (j+1) j) =
        (complex k R M).d (j+1) j ≫ (transportIso k R M h e he (j+1)).hom
      rw [complex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (transport_boundary k R M h e he (j+1) x).symm)

end ArExplicit.ModuleBar

end

end OAI
