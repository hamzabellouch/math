import OAI.Algebra.AuslanderReiten.Fibers.FiberProjectionProfile
import OAI.Algebra.AuslanderReiten.Coordinates.TwoTwistLinear
import Mathlib.Algebra.CharP.Two

namespace OAI

noncomputable section
namespace ArExplicit.TriangleGradedSequence
open CategoryTheory CategoryTheory.Pretriangulated
universe u v w
variable (k : Type u) [Field k] [CharP k 2]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [Limits.HasZeroObject C] [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
variable (T : Triangle C) (hT : T ∈ distTriang C) (X : C)
variable (em : Middle T X 0 ≃ₗ[k] k × k) (et : Top T X 0 ≃ₗ[k] k)
variable (c : k) (hc : c ≠ 0)
variable (hrow : ∀ m, et (second k T X 0 m) = c * ((em m).1 + (em m).2))

include hc hrow in
omit [CharP k 2] [Limits.HasZeroObject C] [Pretriangulated C] in
theorem second_zero_surjective : Function.Surjective (second k T X 0) := by
  intro y
  refine ⟨em.symm (c⁻¹ * et y, 0), et.injective ?_⟩
  rw [hrow, em.apply_symm_apply, add_zero, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

include hT hc hrow in

theorem first_zero_diagonal (x : Bottom T X 0) :
    (em (first k T X 0 x)).1 = (em (first k T X 0 x)).2 := by
  have hz : second k T X 0 (first k T X 0 x) = 0 := by
    have hmem := LinearMap.mem_range_self (first k T X 0) x
    rw [exact_middle k T X hT 0] at hmem
    exact hmem
  have h := hrow (first k T X 0 x)
  rw [hz, map_zero] at h
  exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left hc)

def zeroDiagonalProjection : Bottom T X 0 →ₗ[k] diagonalSubmodule (k := k) (V := k) :=
  (em.toLinearMap.comp (first k T X 0)).codRestrict _
    (first_zero_diagonal k T hT X em et c hc hrow)

variable [Subsingleton (Top T X (-1))]

theorem zeroDiagonalProjection_bijective :
    Function.Bijective (zeroDiagonalProjection k T hT X em et c hc hrow) := by
  constructor
  · intro x y h
    apply first_zero_injective k T hT X
    apply em.injective
    exact congrArg Subtype.val h
  · intro z
    have hz : second k T X 0 (em.symm z.val) = 0 := by
      apply et.injective
      rw [hrow, em.apply_symm_apply, map_zero]
      rw [CharTwo.add_eq_zero.mpr z.property, mul_zero]
    have hm : em.symm z.val ∈ LinearMap.range (first k T X 0) := by
      rw [exact_middle k T X hT 0]
      exact hz
    obtain ⟨x, hx⟩ := hm
    refine ⟨x, Subtype.ext ?_⟩
    change em (first k T X 0 x) = z.val
    rw [hx, em.apply_symm_apply]

def zeroDiagonalEquiv : Bottom T X 0 ≃ₗ[k] diagonalSubmodule (k := k) (V := k) :=
  LinearEquiv.ofBijective (zeroDiagonalProjection k T hT X em et c hc hrow)
    (zeroDiagonalProjection_bijective k T hT X em et c hc hrow)

end ArExplicit.TriangleGradedSequence

namespace ArExplicit
universe u
variable (k : Type u) [Field k]

def scalarDiagonalEquiv : diagonalSubmodule (k := k) (V := k) ≃ₗ[k] k where
  toFun z := z.val.1
  invFun a := ⟨(a,a), rfl⟩
  left_inv z := Subtype.ext (Prod.ext rfl z.property)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end ArExplicit

end

end OAI
