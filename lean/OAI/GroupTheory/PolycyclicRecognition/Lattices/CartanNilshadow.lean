import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanJordanDecomposition
import Mathlib.Algebra.Lie.SemiDirect

namespace OAI

/-! # The nilpotent Lie algebra attached to the Cartan height action

The graph of minus the semisimple height action is a Lie subalgebra of the
affine derivation algebra. Its first coordinate is linearly the original Lie
algebra, while its bracket has the semisimple action removed.
-/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

def cartanNilshadowSubalgebra :
    LieSubalgebra ℝ (L ⋊⁅(LieHom.id : LieDerivation ℝ L L →ₗ⁅ℝ⁆ LieDerivation ℝ L L)⁆
      LieDerivation ℝ L L) where
  carrier := {p | p.right = -heightSemisimpleAction T H p.left}
  zero_mem' := by simp
  add_mem' {p q} hp hq := by
    change p.right + q.right = -heightSemisimpleAction T H (p.left + q.left)
    rw [hp, hq, map_add, neg_add]
  smul_mem' r {p} hp := by
    change r • p.right = -heightSemisimpleAction T H (r • p.left)
    rw [hp, map_smul, smul_neg]
  lie_mem' {p q} hp hq := by
    change ⁅p.right, q.right⁆ = -heightSemisimpleAction T H
      (⁅p.left, q.left⁆ + p.right q.left - q.right p.left)
    rw [hp, hq]
    simp only [neg_lie, lie_neg, heightSemisimpleAction_commute,
      LieDerivation.neg_apply, map_add, map_sub, map_neg,
      heightSemisimpleAction_lie, heightSemisimpleAction_annihilate, neg_zero,
      add_zero, sub_zero]

abbrev CartanNilshadow := cartanNilshadowSubalgebra T H

def cartanNilshadowEquiv : L ≃ₗ[ℝ] CartanNilshadow T H where
  toFun x := ⟨⟨x, -heightSemisimpleAction T H x⟩, rfl⟩
  invFun p := p.val.left
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply SemiDirectSum.ext
    · rfl
    · exact p.property.symm
  map_add' x y := by
    apply Subtype.ext
    apply SemiDirectSum.ext
    · rfl
    · change -heightSemisimpleAction T H (x + y) =
        -heightSemisimpleAction T H x + -heightSemisimpleAction T H y
      rw [map_add, neg_add]
  map_smul' r x := by
    apply Subtype.ext
    apply SemiDirectSum.ext
    · rfl
    · change -heightSemisimpleAction T H (r • x) = r • -heightSemisimpleAction T H x
      rw [map_smul, smul_neg]

instance : FiniteDimensional ℝ (CartanNilshadow T H) :=
  (cartanNilshadowEquiv T H).finiteDimensional

theorem cartanNilshadow_bracket (x y : L) :
    (cartanNilshadowEquiv T H).symm ⁅cartanNilshadowEquiv T H x,
      cartanNilshadowEquiv T H y⁆ =
      ⁅x, y⁆ - heightSemisimpleAction T H x y + heightSemisimpleAction T H y x := by
  change ⁅x, y⁆ + (-heightSemisimpleAction T H x) y -
    (-heightSemisimpleAction T H y) x = _
  simp only [LieDerivation.neg_apply]
  abel

private theorem nilpotent_of_square_eq_mul {V : Type*} [AddCommGroup V] [Module ℝ V]
    {A F : Module.End ℝ V} (hA : IsNilpotent A) (hFF : F * F = A * F) : IsNilpotent F := by
  have hp (k : ℕ) : F ^ (k + 1) = A ^ k * F := by
    induction k with
    | zero => simp
    | succ k hk =>
      calc
        F ^ (k + 1 + 1) = F ^ (k + 1) * F := pow_succ _ _
        _ = A ^ k * (F * F) := by rw [hk, mul_assoc]
        _ = A ^ (k + 1) * F := by rw [hFF, ← mul_assoc, pow_succ]
  obtain ⟨k, hk⟩ := hA
  exact ⟨k + 1, by rw [hp, hk, zero_mul]⟩

/-- The Cartan graph is nilpotent; no nilshadow theorem is assumed. -/
theorem cartanNilshadow_nilpotent : LieRing.IsNilpotent (CartanNilshadow T H) := by
  let e := cartanNilshadowEquiv T H
  apply (LieAlgebra.isNilpotent_iff_forall (R := ℝ)).mpr
  intro p
  obtain ⟨x, rfl⟩ := e.surjective p
  let F : Module.End ℝ L := e.symm.conjRingEquiv (ad ℝ (CartanNilshadow T H) (e x))
  let A : Module.End ℝ L := ad ℝ L x - (heightSemisimpleAction T H x).toLinearMap
  have hF (y : L) : F y = ⁅x, y⁆ - heightSemisimpleAction T H x y +
      heightSemisimpleAction T H y x := cartanNilshadow_bracket T H x y
  have hFh (y : L) : heightProjection T.character (F y) = 0 := by
    rw [hF, map_add, map_sub, T.height_lie, heightSemisimpleAction_height_zero,
      heightSemisimpleAction_height_zero, sub_self, add_zero]
  have hFr (y : L) (hy : heightProjection T.character y = 0) : F y = A y := by
    have hs : heightSemisimpleAction T H y = 0 := by
      change cartanWeightDerivationLinear T H
        (cartanHeightSection T H (heightProjection T.character y)) = 0
      rw [hy, map_zero, map_zero]
    rw [hF, hs, LieDerivation.zero_apply, add_zero]
    rfl
  have hFF : F * F = A * F := by
    ext y
    exact hFr (F y) (hFh y)
  obtain ⟨k, hk⟩ := nilpotent_of_square_eq_mul (heightReducedAdjoint_nilpotent T H x) hFF
  refine ⟨k, e.symm.conjRingEquiv.injective ?_⟩
  rw [map_pow, map_zero]
  exact hk

end PolycyclicRecognition

end

end OAI
