import OAI.Algebra.Finitistic.Ordinary.OrdinaryProductProjective
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Tactic.Abel

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R]

abbrev secondInflation : ModuleCat.{v} R ⥤ ModuleCat.{v} (L × R) :=
  ModuleCat.restrictScalars (RingHom.snd L R)

abbrev swapModule (M : ModuleCat.{v} (L × R)) : ModuleCat.{v} (R × L) :=
  (ModuleCat.restrictScalars (RingEquiv.prodComm : R × L ≃+* L × R).toRingHom).obj M

abbrev secondObject (M : ModuleCat.{v} (L × R)) : ModuleCat.{v} R :=
  firstObject R L (swapModule L R M)

abbrev pairObject (M : ModuleCat.{v} (L × R)) : ModuleCat.{v} (L × R) := ModuleCat.of (L × R)
  (((firstInflation L R).obj (firstObject L R M)) × ((secondInflation L R).obj (secondObject L R M)))

variable (M : ModuleCat.{v} (L × R))

def splitTo : M →ₗ[L × R] pairObject L R M where
  toFun m := (⟨((1,0) : L × R) • m, by
    change ((1,0) : L × R) • (((1,0) : L × R) • m) = ((1,0) : L × R) • m
    rw [← mul_smul]
    have h : ((1,0) : L × R) * (1,0) = (1,0) := by ext <;> simp
    rw [h]⟩, ⟨((0,1) : L × R) • m, by
    change ((0,1) : L × R) • (((0,1) : L × R) • m) = ((0,1) : L × R) • m
    rw [← mul_smul]
    have h : ((0,1) : L × R) * (0,1) = (0,1) := by ext <;> simp
    rw [h]⟩)
  map_add' x y := Prod.ext (Subtype.ext (smul_add _ _ _)) (Subtype.ext (smul_add _ _ _))
  map_smul' d m := by
    apply Prod.ext
    · apply Subtype.ext
      change ((1,0) : L × R) • (d • m) = ((d.1,0) : L × R) • (((1,0) : L × R) • m)
      rw [← mul_smul,← mul_smul]
      congr 1
      ext <;> simp
    · apply Subtype.ext
      change ((0,1) : L × R) • (d • m) = ((0,d.2) : L × R) • (((0,1) : L × R) • m)
      rw [← mul_smul,← mul_smul]
      congr 1
      ext <;> simp

def joinTo : pairObject L R M →ₗ[L × R] M where
  toFun x := x.1.val + (show M from x.2.val)
  map_add' x y := by
    change (x.1.val+y.1.val) + ((show M from x.2.val)+(show M from y.2.val)) =
      (x.1.val+(show M from x.2.val)) + (y.1.val+(show M from y.2.val))
    abel
  map_smul' d x := by
    have h₁ := firstSpace_product_smul L R d x.1
    have h₂ := firstSpace_product_smul R L (M := swapModule L R M) (d.2,d.1) x.2
    change ((d.1,0) : L × R) • x.1.val + ((0,d.2) : L × R) • (show M from x.2.val) = d • (x.1.val + (show M from x.2.val))
    rw [smul_add,← h₁]
    exact congrArg (fun y : swapModule L R M => d • x.1.val + (show M from y)) h₂.symm

/-- Every module over a product ring splits into its two actual central-idempotent components. -/
def splitting : M ≃ₗ[L × R] pairObject L R M where
  __ := splitTo L R M
  invFun := joinTo L R M
  left_inv m := by
    change ((1,0) : L × R) • m + ((0,1) : L × R) • m = m
    rw [← add_smul]
    have h : ((1,0) : L × R) + (0,1) = 1 := by ext <;> simp
    rw [h,one_smul]
  right_inv x := by
    have h₁ : ((1,0) : L × R) • x.1.val = x.1.val := x.1.property
    have h₂ : ((0,1) : L × R) • (show M from x.2.val) = (show M from x.2.val) := x.2.property
    have hz₁ : ((0,1) : L × R) • x.1.val = 0 := by
      calc
        _ = ((0,1) : L × R) • (((1,0) : L × R) • x.1.val) := by rw [h₁]
        _ = 0 := by
          rw [← mul_smul]
          have h : ((0,1) : L × R) * (1,0) = 0 := by ext <;> simp
          rw [h,zero_smul]
    have hz₂ : ((1,0) : L × R) • (show M from x.2.val) = 0 := by
      calc
        _ = ((1,0) : L × R) • (((0,1) : L × R) • (show M from x.2.val)) := by rw [h₂]
        _ = 0 := by
          rw [← mul_smul]
          have h : ((1,0) : L × R) * (0,1) = 0 := by ext <;> simp
          rw [h,zero_smul]
    apply Prod.ext
    · apply Subtype.ext
      change ((1,0) : L × R) • (x.1.val + (show M from x.2.val)) = x.1.val
      rw [smul_add,h₁,hz₂,add_zero]
    · apply Subtype.ext
      change ((0,1) : L × R) • (x.1.val + (show M from x.2.val)) = (show M from x.2.val)
      rw [smul_add,hz₁,h₂,zero_add]
end LittleFinitistic.ProductModules

end

end OAI
