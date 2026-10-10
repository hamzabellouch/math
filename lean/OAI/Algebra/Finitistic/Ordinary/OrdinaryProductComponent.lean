import OAI.Algebra.Finitistic.Ordinary.OrdinaryRestrictionHomology
import Mathlib.Algebra.Category.ModuleCat.Projective

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R]
variable (M : ModuleCat.{v} (L × R))

/-- The actual first central-idempotent summand of an arbitrary product-ring module. -/
def firstSpace : Submodule (L × R) M where
  carrier := {m | ((1,0) : L × R) • m = m}
  zero_mem' := smul_zero _
  add_mem' {x y} hx hy := by
    change ((1,0) : L × R) • (x+y) = x+y
    rw [smul_add,hx,hy]
  smul_mem' d x hx := by
    change ((1,0) : L × R) • (d • x) = d • x
    have he : ((1,0) : L × R) * d = d * (1,0) := by ext <;> simp
    rw [← mul_smul,he,mul_smul,hx]

def firstScalar (r : L) : firstSpace L R M →ₗ[ℤ] firstSpace L R M where
  toFun x := ⟨(r,(0:R)) • x.val, by
    change ((1,0) : L × R) • ((r,(0:R)) • x.val) = (r,(0:R)) • x.val
    rw [← mul_smul]
    have h : ((1,0) : L × R) * (r,(0:R)) = (r,(0:R)) := by ext <;> simp
    rw [h]⟩
  map_add' x y := Subtype.ext (smul_add _ _ _)
  map_smul' n x := by
    apply Subtype.ext
    exact smul_comm ((r,(0:R)) : L × R) n x.val

def firstAction : L →+* Module.End ℤ (firstSpace L R M) where
  toFun := firstScalar L R M
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((1,0) : L × R) • x.val = x.val
    exact x.property
  map_zero' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (0 : L × R) • x.val = 0
    exact zero_smul (L × R) x.val
  map_add' r s := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((r+s,(0:R)) : L × R) • x.val = (r,(0:R)) • x.val + (s,(0:R)) • x.val
    simpa only [Prod.mk_add_mk,add_zero] using add_smul ((r,(0:R)) : L × R) (s,(0:R)) x.val
  map_mul' r s := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((r*s,(0:R)) : L × R) • x.val = (r,(0:R)) • ((s,(0:R)) • x.val)
    rw [← mul_smul]
    have h : ((r,(0:R)) : L × R) * (s,0) = (r*s,0) := by ext <;> simp
    rw [h]

instance firstModule : Module L (firstSpace L R M) := Module.compHom _ (firstAction L R M)

abbrev firstObject : ModuleCat.{v} L := ModuleCat.of L (firstSpace L R M)

variable {M} {N : ModuleCat.{v} (L × R)}

def firstMap (f : M ⟶ N) : firstSpace L R M →ₗ[L] firstSpace L R N where
  toFun x := ⟨f.hom x.val, by
    change ((1,0) : L × R) • f.hom x.val = f.hom x.val
    rw [← f.hom.map_smul,x.property]⟩
  map_add' x y := Subtype.ext (f.hom.map_add _ _)
  map_smul' r x := Subtype.ext (f.hom.map_smul ((r,(0:R)) : L × R) x.val)

/-- The actual component functor, constructed on every module and map. -/
def firstFunctor : ModuleCat.{v} (L × R) ⥤ ModuleCat.{v} L where
  obj M := firstObject L R M
  map f := ModuleCat.ofHom (firstMap L R f)
  map_id M := by rfl
  map_comp f g := by rfl

/-- Surjections remain surjections on the selected component, by projecting a preimage. -/
theorem firstMap_surjective (f : M ⟶ N) (hf : Function.Surjective f.hom) :
    Function.Surjective (firstMap L R f) := by
  intro y
  obtain ⟨x,hx⟩ := hf y.val
  refine ⟨⟨((1,0) : L × R) • x,?_⟩,?_⟩
  · change ((1,0) : L × R) • (((1,0) : L × R) • x) = ((1,0) : L × R) • x
    rw [← mul_smul]
    have h : ((1,0) : L × R) * (1,0) = (1,0) := by ext <;> simp
    rw [h]
  · apply Subtype.ext
    change f.hom (((1,0) : L × R) • x) = y.val
    rw [f.hom.map_smul,hx,y.property]
end LittleFinitistic.ProductModules

end

end OAI
