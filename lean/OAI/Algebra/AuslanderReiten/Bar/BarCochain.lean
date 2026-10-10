import OAI.Algebra.AuslanderReiten.Bar.BarResolution
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.CategoryTheory.Abelian.Projective.Ext

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

abbrev Cochain3 := R →ₗ[k] R →ₗ[k] R →ₗ[k] R

def suffix3 (p : Cochain3 k R) : object k R 3 →ₗ[k] R :=
  TensorProduct.lift {
    toFun := fun a => TensorProduct.lift {
      toFun := fun b => TensorProduct.lift ((LinearMap.mul k R).comp (p a b))
      map_add' := by
        intro b c
        apply TensorProduct.ext'
        intro d e
        simp
      map_smul' := by
        intro t b
        apply TensorProduct.ext'
        intro d e
        simp }
    map_add' := by
      intro a b
      apply TensorProduct.ext'
      intro c y
      induction y using TensorProduct.inductionOn with
      | add y z hy hz =>
        simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply] at *
        rw [hy, hz]
      | tmul d e => simp
    map_smul' := by
      intro t a
      apply TensorProduct.ext'
      intro b y
      induction y using TensorProduct.inductionOn with
      | add y z hy hz =>
        simp only [TensorProduct.tmul_add, map_add, LinearMap.smul_apply] at *
        rw [hy, hz]
      | tmul c d => simp }

@[simp] theorem suffix3_tmul (p : Cochain3 k R) (a b c d : R) :
    suffix3 k R p (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] d))) = p a b c * d := rfl

def cochain3Linear (p : Cochain3 k R) : object k R 4 →ₗ[k] R :=
  TensorProduct.lift ((LinearMap.mul k R).compl₂ (suffix3 k R p))

@[simp] theorem cochain3Linear_tmul (p : Cochain3 k R) (a b c d e : R) :
    cochain3Linear k R p (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] (d ⊗ₜ[k] e)))) =
      a * p b c d * e := by
  change a * (p b c d * e) = _
  exact (mul_assoc _ _ _).symm

def bimoduleMap {n m : ℕ} (f : object k R n →ₗ[k] object k R m)
    (hl : ∀ a x, f (left k R n a x) = left k R m a (f x))
    (hr : ∀ a x, f (right k R n a x) = right k R m a (f x)) :
    moduleObject k R n →ₗ[Enveloping k R] moduleObject k R m where
  toAddHom := f.toAddHom
  map_smul' a x := by
    let y : object k R n := x
    change f (representation k R n a y) = representation k R m a (f y)
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | tmul a b =>
      change f (left k R n a (right k R n b y)) =
        left k R m a (right k R m b (f y))
      rw [hl, hr]

theorem cochain3Linear_left (p : Cochain3 k R) (a : R) (x : object k R 4) :
    cochain3Linear k R p (left k R 4 a x) = a * cochain3Linear k R p x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  | tmul b x => exact mul_assoc _ _ _

theorem suffix3_right (p : Cochain3 k R) (a : Rᵐᵒᵖ) (x : object k R 3) :
    suffix3 k R p (right k R 3 a x) = suffix3 k R p x * MulOpposite.unop a := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, add_mul]
  | tmul b y =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, TensorProduct.tmul_add, hy, hz, add_mul]
    | tmul c z =>
      induction z using TensorProduct.inductionOn with
      | add z w hz hw => simp only [map_add, TensorProduct.tmul_add, hz, hw, add_mul]
      | tmul d e => exact (mul_assoc _ _ _).symm

theorem cochain3Linear_right (p : Cochain3 k R) (a : Rᵐᵒᵖ) (x : object k R 4) :
    cochain3Linear k R p (right k R 4 a x) =
      cochain3Linear k R p x * MulOpposite.unop a := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, add_mul]
  | tmul b y =>
    change b * suffix3 k R p (right k R 3 a y) =
      (b * suffix3 k R p y) * MulOpposite.unop a
    rw [suffix3_right, mul_assoc]

def cochain3 (p : Cochain3 k R) : moduleObject k R 4 →ₗ[Enveloping k R] moduleObject k R 0 :=
  bimoduleMap k R (cochain3Linear k R p) (cochain3Linear_left k R p) (cochain3Linear_right k R p)

def IsCocycle3 (p : Cochain3 k R) : Prop :=
  ∀ a b c d, a * p b c d + p (a * b) c d + p a (b * c) d +
    p a b (c * d) + p a b c * d = 0

theorem cochain3_boundary_tmul (p : Cochain3 k R) (a b c d e f : R) :
    cochain3Linear k R p (boundary k R 4
      (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] (d ⊗ₜ[k] (e ⊗ₜ[k] f)))))) =
      a * (b * p c d e + p (b * c) d e + p b (c * d) e +
        p b c (d * e) + p b c d * e) * f := by
  simp only [boundary_succ_tmul k R 3, boundary_succ_tmul k R 2,
    boundary_succ_tmul k R 1, boundary_succ_tmul k R 0, boundary_zero_tmul k R,
    left_tmul k R 3, left_tmul k R 2, left_tmul k R 1, left_tmul k R 0,
    TensorProduct.tmul_add, map_add, cochain3Linear_tmul k R p, mul_add, add_mul, mul_assoc]
  abel

theorem cochain3_closed (p : Cochain3 k R) (hp : IsCocycle3 k R p) :
    (cochain3Linear k R p).comp (boundary k R 4) = 0 := by
  ext a b c d e f
  change cochain3Linear k R p (boundary k R 4
    (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] (d ⊗ₜ[k] (e ⊗ₜ[k] f)))))) = 0
  rw [cochain3_boundary_tmul, hp]
  simp

variable [CharP k 2]

theorem cochain3_cycle (p : Cochain3 k R) (hp : IsCocycle3 k R p) :
    (complex k R).d 4 3 ≫ ModuleCat.ofHom
      (X := moduleObject k R 4) (Y := moduleObject k R 0) (cochain3 k R p) = 0 := by
  rw [complex_d k R 3]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (cochain3_closed k R p hp) x

def extClass3 (p : Cochain3 k R) (hp : IsCocycle3 k R p) :
    CategoryTheory.Abelian.Ext (moduleObject k R 0) (moduleObject k R 0) 3 :=
  (resolution k R).extMk
    (ModuleCat.ofHom (X := moduleObject k R 4) (Y := moduleObject k R 0) (cochain3 k R p))
    4 rfl (cochain3_cycle k R p hp)

theorem extClass3_eq_zero_iff (p : Cochain3 k R) (hp : IsCocycle3 k R p) :
    extClass3 k R p hp = 0 ↔
      ∃ g : moduleObject k R 3 →ₗ[Enveloping k R] moduleObject k R 0,
        g.comp (differential k R 3) = cochain3 k R p := by
  trans ∃ g : (complex k R).X 2 ⟶ moduleObject k R 0,
      (complex k R).d 3 2 ≫ g = ModuleCat.ofHom
        (X := moduleObject k R 4) (Y := moduleObject k R 0) (cochain3 k R p)
  · exact (resolution k R).extMk_eq_zero_iff _ 4 rfl _ 2 rfl
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g.hom, ?_⟩
    rw [show (complex k R).d 3 2 =
      ModuleCat.ofHom (X := moduleObject k R 4) (Y := moduleObject k R 3)
        (differential k R 3) from complex_d k R 2] at hg
    exact congrArg ModuleCat.Hom.hom hg
  · rintro ⟨g, hg⟩
    refine ⟨ModuleCat.ofHom (X := moduleObject k R 3) (Y := moduleObject k R 0) g, ?_⟩
    rw [complex_d k R 2]
    apply ModuleCat.hom_ext
    exact hg

end ArExplicit.AbsoluteBar

end

end OAI
