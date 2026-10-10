import OAI.NumberTheory.Ostmann.Tree.CycleCut
import OAI.NumberTheory.Ostmann.Tree.DensityHorizontal

namespace OAI

namespace Ostmann.Tree
noncomputable section
open scoped BigOperators
open Ostmann.Arithmetic.ResidueHaar
open Ostmann.Arithmetic.GroupHaarImage

local instance fieldDecidableEq {F : Type*} [Field F] : DecidableEq F := Classical.decEq F

local instance subgroupFintype {G : Type*} [Group G] [Fintype G] (S : Subgroup G) :
    Fintype S := Fintype.ofFinite _
local instance fiberFintype {A B : Type*} [Fintype A] (f : A → B) (y : B) :
    Fintype {x : A // f x=y} := Fintype.ofFinite _

def fiberAverage {A B : Type*} [Fintype A] (f : A → B) (F : A → ℂ) (y : B) : ℂ :=
  average (fun x : {x : A // f x=y} => F x.val)

def kernelFiberEquiv {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) (y : B) : f.ker ≃ {x : A // f x=y} where
  toFun k := ⟨Classical.choose (hf y)*k.val,by
    rw [map_mul,Classical.choose_spec (hf y),show f k.val=1 from k.property,mul_one]⟩
  invFun x := ⟨(Classical.choose (hf y))⁻¹*x.val,by
    change f ((Classical.choose (hf y))⁻¹*x.val)=1
    rw [map_mul,map_inv,Classical.choose_spec (hf y),x.property,inv_mul_cancel]⟩
  left_inv k := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

theorem average_product_nested {I J : Type*} [Fintype I] [Fintype J]
    (F : I × J → ℂ) : average F=average (fun i => average (fun j => F (i,j))) := by
  simp only [average,Fintype.card_prod,Nat.cast_mul,mul_inv_rev,Fintype.sum_prod_type,
    ← Finset.mul_sum]
  ring

theorem average_fiberAverage {A B : Type*} [Group A] [Group B] [Fintype A] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f) (F : A → ℂ) :
    average F=average (fiberAverage f F) := by
  have he := average_equiv (homProductEquiv f hf).symm F
  calc
    average F = average (fun z : B × f.ker => F (Classical.choose (hf z.1)*z.2.val)) := he.symm
    _ = average (fun y : B => average (fun k : f.ker => F (Classical.choose (hf y)*k.val))) :=
      average_product_nested _
    _ = average (fiberAverage f F) := by
      congr 1
      funext y
      exact average_equiv (kernelFiberEquiv f hf y) (fun x => F x.val)

theorem cut_fiber_average {F : Type*} [Field F] [Fintype F] {d k : ℕ}
    (C : Density.Cut d k) (W : (Leaves d → Fˣ) → ℂ) :
    average W = average (fiberAverage C.project W) :=
  average_fiberAverage (C.projectHom) C.project_surjective W

end
end Ostmann.Tree

end OAI
