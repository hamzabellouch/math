import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorMap
import Mathlib.Algebra.Module.Projective

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor

universe u
variable {k R F G Q X : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [IsScalarTower k Rᵐᵒᵖ F]
variable [AddCommGroup G] [Module k G] [Module Rᵐᵒᵖ G] [IsScalarTower k Rᵐᵒᵖ G]
variable [AddCommGroup Q] [Module k Q] [Module Rᵐᵒᵖ Q] [IsScalarTower k Rᵐᵒᵖ Q]
variable [AddCommGroup X] [Module k X] [Module R X] [IsScalarTower k R X]

def mapFirst (X : Type u) [AddCommGroup X] [Module k X] [Module R X]
    (f : F →ₗ[Rᵐᵒᵖ] G) : BalancedTensor k R F X →ₗ[k] BalancedTensor k R G X :=
  map (f.restrictScalars k) (LinearMap.id : X →ₗ[k] X)
    (fun a x => f.map_smul a x) (fun _ _ => rfl)

omit [IsScalarTower k R X] in
@[simp] theorem mapFirst_tmul (f : F →ₗ[Rᵐᵒᵖ] G) (m : F) (x : X) :
    mapFirst (k := k) X f (tmul m x) = tmul (f m) x := rfl

omit [IsScalarTower k R X] in
@[simp] theorem mapFirst_id : mapFirst (k := k) X (LinearMap.id : F →ₗ[Rᵐᵒᵖ] F) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using induction_on with
  | zero => simp
  | tmul f x => rfl
  | add z w hz hw => simp_all

omit [IsScalarTower k R X] in
@[simp] theorem mapFirst_comp (f : F →ₗ[Rᵐᵒᵖ] G) (g : G →ₗ[Rᵐᵒᵖ] Q) :
    mapFirst (k := k) X (g.comp f) = (mapFirst (k := k) X g).comp (mapFirst (k := k) X f) := by
  apply LinearMap.ext
  intro z
  induction z using induction_on with
  | zero => simp
  | tmul f x => rfl
  | add z w hz hw => simp_all

omit [IsScalarTower k R X] in
@[simp] theorem mapFirst_add (f g : F →ₗ[Rᵐᵒᵖ] G) :
    mapFirst (k := k) X (f + g) = mapFirst (k := k) X f + mapFirst (k := k) X g := by
  apply LinearMap.ext
  intro z
  induction z using induction_on with
  | zero => simp
  | tmul f x => simp [BalancedTensor.add_tmul]
  | add z w hz hw => simp_all [add_left_comm, add_comm]

omit [IsScalarTower k R X] in
@[simp] theorem mapFirst_zero : mapFirst (k := k) X (0 : F →ₗ[Rᵐᵒᵖ] G) = 0 := by
  apply LinearMap.ext
  intro z
  induction z using induction_on with
  | zero => simp
  | tmul f x => simp
  | add z w hz hw => simp_all

theorem exists_splitting (f : F →ₗ[Rᵐᵒᵖ] G) (g : G →ₗ[Rᵐᵒᵖ] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (he : LinearMap.range f = LinearMap.ker g) [Module.Projective Rᵐᵒᵖ Q] :
    ∃ c : G →ₗ[Rᵐᵒᵖ] F, ∃ s : Q →ₗ[Rᵐᵒᵖ] G,
      c.comp f = LinearMap.id ∧ g.comp s = LinearMap.id ∧
        f.comp c + s.comp g = LinearMap.id := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g (LinearMap.id : Q →ₗ[Rᵐᵒᵖ] Q) hg
  let e : F ≃ₗ[Rᵐᵒᵖ] LinearMap.range f := LinearEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hf (congrArg Subtype.val h), by
      rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩⟩
  let r : G →ₗ[Rᵐᵒᵖ] LinearMap.range f :=
    { toFun := fun y => ⟨y - s (g y), by
        rw [he]
        change g (y - s (g y)) = 0
        rw [map_sub, show g (s (g y)) = g y from DFunLike.congr_fun hs (g y), sub_self]⟩
      map_add' a b := by
        apply Subtype.ext
        change a + b - s (g (a + b)) = (a - s (g a)) + (b - s (g b))
        simp only [map_add, add_sub_add_comm]
      map_smul' a b := by
        apply Subtype.ext
        change a • b - s (g (a • b)) = a • (b - s (g b))
        simp only [map_smul, smul_sub] }
  let c : G →ₗ[Rᵐᵒᵖ] F := e.symm.toLinearMap.comp r
  have hc (y : G) : f (c y) = y - s (g y) := by
    exact congrArg Subtype.val (e.apply_symm_apply (r y))
  have hgf : g.comp f = 0 := LinearMap.range_le_ker_iff.mp he.le
  refine ⟨c, s, ?_, hs, ?_⟩
  · apply LinearMap.ext
    intro x
    apply hf
    rw [LinearMap.comp_apply, hc]
    have hz : g (f x) = 0 := DFunLike.congr_fun hgf x
    simp [hz]
  · apply LinearMap.ext
    intro y
    change f (c y) + s (g y) = y
    rw [hc, sub_add_cancel]

omit [IsScalarTower k R X] in
theorem mapFirst_shortExact (f : F →ₗ[Rᵐᵒᵖ] G) (g : G →ₗ[Rᵐᵒᵖ] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (he : LinearMap.range f = LinearMap.ker g) [Module.Projective Rᵐᵒᵖ Q] :
    Function.Injective (mapFirst (k := k) X f) ∧ Function.Surjective (mapFirst (k := k) X g) ∧
      LinearMap.range (mapFirst (k := k) X f) = LinearMap.ker (mapFirst (k := k) X g) := by
  obtain ⟨c, s, hcf, hgs, hsum⟩ := exists_splitting f g hf hg he
  have hcf' : (mapFirst (k := k) X c).comp (mapFirst (k := k) X f) = LinearMap.id := by
    rw [← mapFirst_comp, hcf, mapFirst_id]
  have hgs' : (mapFirst (k := k) X g).comp (mapFirst (k := k) X s) = LinearMap.id := by
    rw [← mapFirst_comp, hgs, mapFirst_id]
  have hsum' : (mapFirst (k := k) X f).comp (mapFirst (k := k) X c) +
      (mapFirst (k := k) X s).comp (mapFirst (k := k) X g) = LinearMap.id := by
    rw [← mapFirst_comp, ← mapFirst_comp, ← mapFirst_add, hsum, mapFirst_id]
  have hgf : g.comp f = 0 := LinearMap.range_le_ker_iff.mp he.le
  have hgf' : (mapFirst (k := k) X g).comp (mapFirst (k := k) X f) = 0 := by
    rw [← mapFirst_comp, hgf, mapFirst_zero]
  refine ⟨?_, ?_, le_antisymm (LinearMap.range_le_ker_iff.mpr hgf') ?_⟩
  · intro x y hxy
    have hx := DFunLike.congr_fun hcf' x
    have hy := DFunLike.congr_fun hcf' y
    change mapFirst (k := k) X c (mapFirst (k := k) X f x) = x at hx
    change mapFirst (k := k) X c (mapFirst (k := k) X f y) = y at hy
    rw [← hx, ← hy, hxy]
  · intro z
    exact ⟨mapFirst (k := k) X s z, DFunLike.congr_fun hgs' z⟩
  · intro z hz
    refine ⟨mapFirst (k := k) X c z, ?_⟩
    have h := DFunLike.congr_fun hsum' z
    change mapFirst (k := k) X f (mapFirst (k := k) X c z) + mapFirst (k := k) X s (mapFirst (k := k) X g z) = z at h
    simpa only [show mapFirst (k := k) X g z = 0 from hz, map_zero, add_zero] using h

end ArExplicit.BalancedTensor

end

end OAI
