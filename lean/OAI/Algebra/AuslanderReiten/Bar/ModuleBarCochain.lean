import OAI.Algebra.AuslanderReiten.Bar.ModuleBar
import OAI.Algebra.AuslanderReiten.Bar.BarCochain

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

def suffix3 (p : AbsoluteBar.Cochain3 k R) : object k R M 3 →ₗ[k] M :=
  TensorProduct.lift {
    toFun := fun a => TensorProduct.lift {
      toFun := fun b => TensorProduct.lift (((Algebra.lsmul k k M).toLinearMap).comp (p a b))
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

@[simp] theorem suffix3_tmul (p : AbsoluteBar.Cochain3 k R) (a b c : R) (d : M) :
    suffix3 k R M p (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] d))) = p a b c • d := rfl

def cochain3Linear (p : AbsoluteBar.Cochain3 k R) : object k R M 4 →ₗ[k] M :=
  TensorProduct.lift (((Algebra.lsmul k k M).toLinearMap).compl₂ (suffix3 k R M p))

@[simp] theorem cochain3Linear_tmul (p : AbsoluteBar.Cochain3 k R) (a b c d : R) (e : M) :
    cochain3Linear k R M p (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] (d ⊗ₜ[k] e)))) =
      (a * p b c d) • e := by
  change a • (p b c d • e) = _
  exact (mul_smul _ _ _).symm

theorem cochain3Linear_left (p : AbsoluteBar.Cochain3 k R) (a : R) (x : object k R M 4) :
    cochain3Linear k R M p (left k R M 4 a x) = a • cochain3Linear k R M p x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul b x => exact mul_smul _ _ _

def cochain3 (p : AbsoluteBar.Cochain3 k R) :
    moduleObject k R M 4 →ₗ[R] moduleObject k R M 0 where
  toAddHom := (cochain3Linear k R M p).toAddHom
  map_smul' a x := cochain3Linear_left k R M p a x

theorem cochain3_boundary_tmul (p : AbsoluteBar.Cochain3 k R) (a b c d e : R) (m : M) :
    cochain3Linear k R M p (boundary k R M 4
      (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] (d ⊗ₜ[k] (e ⊗ₜ[k] m)))))) =
      (a * (b * p c d e + p (b * c) d e + p b (c * d) e +
        p b c (d * e) + p b c d * e)) • m := by
  simp only [boundary_succ_tmul k R M 3, boundary_succ_tmul k R M 2,
    boundary_succ_tmul k R M 1, boundary_succ_tmul k R M 0, boundary_zero_tmul k R M,
    left_tmul k R M 3, left_tmul k R M 2, left_tmul k R M 1, left_tmul k R M 0,
    TensorProduct.tmul_add, map_add, cochain3Linear_tmul k R M p,
    mul_smul, add_smul, smul_add]
  abel

theorem cochain3_closed (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p) :
    (cochain3Linear k R M p).comp (boundary k R M 4) = 0 := by
  ext a b c d e m
  change cochain3Linear k R M p (boundary k R M 4
    (a ⊗ₜ[k] (b ⊗ₜ[k] (c ⊗ₜ[k] (d ⊗ₜ[k] (e ⊗ₜ[k] m)))))) = 0
  rw [cochain3_boundary_tmul, hp]
  simp

variable [CharP k 2]

theorem cochain3_cycle (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p) :
    (complex k R M).d 4 3 ≫ ModuleCat.ofHom
      (X := moduleObject k R M 4) (Y := moduleObject k R M 0) (cochain3 k R M p) = 0 := by
  rw [complex_d k R M 3]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (cochain3_closed k R M p hp) x

def extClass3 (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p) :
    CategoryTheory.Abelian.Ext (moduleObject k R M 0) (moduleObject k R M 0) 3 :=
  (resolution k R M).extMk
    (ModuleCat.ofHom (X := moduleObject k R M 4) (Y := moduleObject k R M 0) (cochain3 k R M p))
    4 rfl (cochain3_cycle k R M p hp)

theorem extClass3_eq_zero_iff (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p) :
    extClass3 k R M p hp = 0 ↔
      ∃ g : moduleObject k R M 3 →ₗ[R] moduleObject k R M 0,
        g.comp (differential k R M 3) = cochain3 k R M p := by
  trans ∃ g : (complex k R M).X 2 ⟶ moduleObject k R M 0,
      (complex k R M).d 3 2 ≫ g = ModuleCat.ofHom
        (X := moduleObject k R M 4) (Y := moduleObject k R M 0) (cochain3 k R M p)
  · exact (resolution k R M).extMk_eq_zero_iff _ 4 rfl _ 2 rfl
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g.hom, ?_⟩
    rw [complex_d k R M 2] at hg
    exact congrArg ModuleCat.Hom.hom hg
  · rintro ⟨g, hg⟩
    refine ⟨ModuleCat.ofHom (X := moduleObject k R M 3) (Y := moduleObject k R M 0) g, ?_⟩
    rw [complex_d k R M 2]
    apply ModuleCat.hom_ext
    exact hg

theorem extClass3_ne_zero_of_detector (p : AbsoluteBar.Cochain3 k R)
    (hp : AbsoluteBar.IsCocycle3 k R p) (x : moduleObject k R M 4)
    (hx : cochain3 k R M p x ≠ 0)
    (hboundary : ∀ g : moduleObject k R M 3 →ₗ[R] moduleObject k R M 0,
      g (differential k R M 3 x) = 0) : extClass3 k R M p hp ≠ 0 := by
  intro h
  obtain ⟨g, hg⟩ := (extClass3_eq_zero_iff k R M p hp).mp h
  apply hx
  rw [← hg]
  exact hboundary g

end ArExplicit.ModuleBar

end

end OAI
