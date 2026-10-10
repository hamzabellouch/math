import OAI.Algebra.AuslanderReiten.Fibers.FiberProjectionZero

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
variable [Subsingleton (Top T X (-1))]

def zeroScalarEquiv : Bottom T X 0 ≃ₗ[k] k :=
  (zeroDiagonalEquiv k T hT X em et c hc hrow).trans (scalarDiagonalEquiv k)

def diagonalGenerator : Bottom T X 0 :=
  (zeroScalarEquiv k T hT X em et c hc hrow).symm 1

@[simp] theorem zeroScalarEquiv_diagonalGenerator :
    zeroScalarEquiv k T hT X em et c hc hrow (diagonalGenerator k T hT X em et c hc hrow) = 1 :=
  LinearEquiv.apply_symm_apply _ _

theorem diagonalGenerator_image :
    em (first k T X 0 (diagonalGenerator k T hT X em et c hc hrow)) = (1,1) := by
  have h := congrArg Subtype.val
    ((zeroDiagonalEquiv k T hT X em et c hc hrow).apply_symm_apply
      ((scalarDiagonalEquiv k).symm 1))
  exact h

theorem diagonalGenerator_ne_zero : diagonalGenerator k T hT X em et c hc hrow ≠ 0 := by
  intro hz
  have h := zeroScalarEquiv_diagonalGenerator k T hT X em et c hc hrow
  rw [hz, map_zero] at h
  exact zero_ne_one h

theorem eq_scalar_diagonalGenerator (z : Bottom T X 0) :
    z = zeroScalarEquiv k T hT X em et c hc hrow z •
      diagonalGenerator k T hT X em et c hc hrow := by
  apply (zeroScalarEquiv k T hT X em et c hc hrow).injective
  rw [map_smul, zeroScalarEquiv_diagonalGenerator]
  exact (mul_one _).symm

end ArExplicit.TriangleGradedSequence

end

end OAI
