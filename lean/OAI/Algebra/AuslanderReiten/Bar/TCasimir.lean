import OAI.Algebra.AuslanderReiten.Cocycles.CocycleTwist
import OAI.Algebra.AuslanderReiten.Bar.BarCasimir
import Mathlib.LinearAlgebra.TensorProduct.Pi

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q

@[simp] theorem star_star (i : TIndex) : i.star.star = i := by
  obtain ⟨b, i⟩ := i
  cases b <;> rfl

theorem trace_mul_star (a : R) (i : TIndex) :
    TrivialExtension.trace (a * vector q i.star) = coefficient q i a := by
  obtain ⟨b, i⟩ := i
  cases b <;> simp [TIndex.star, vector, lower, upper,
    TrivialExtension.inl, TrivialExtension.inr, coefficient, coordinateFunctional]
  rfl

theorem trace_vector_star (i j : TIndex) :
    TrivialExtension.trace (vector q i * vector q j.star) = if i = j then 1 else 0 := by
  rw [trace_mul_star]
  simp only [coefficient_vector, eq_comm]

def tensorRightCoordinates : R ⊗[k] R ≃ₗ[k] (TIndex → R) :=
  (TensorProduct.congr (LinearEquiv.refl k R) (coordinateEquiv q)).trans
    (TensorProduct.piScalarRight k k R TIndex)

@[simp] theorem tensorRightCoordinates_tmul (a b : R) (i : TIndex) :
    tensorRightCoordinates q (a ⊗ₜ[k] b) i = coefficient q i b • a := by
  simp [tensorRightCoordinates, coordinateEquiv]

def twistedCasimir (H : kˣ) : AbsoluteBar.object k R 1 :=
  ∑ i : TIndex, TrivialExtension.twist H (vector q i) ⊗ₜ[k] vector q i.star

theorem twistedCasimir_coordinates (H : kˣ) (i : TIndex) :
    tensorRightCoordinates q (twistedCasimir q H) i =
      TrivialExtension.twist H (vector q i.star) := by
  simp only [twistedCasimir, map_sum, Finset.sum_apply, tensorRightCoordinates_tmul,
    coefficient_vector]
  rw [Finset.sum_eq_single i.star]
  · simp
  · intro j _ hj
    have hn : i ≠ j.star := by
      intro h
      have := congrArg TIndex.star h
      simp only [star_star] at this
      exact hj this.symm
    simp [hn]
  · simp

private theorem coefficient_right_product (a : R) (i j : TIndex) :
    coefficient q i (vector q j.star * a) = coefficient q j (a * vector q i.star) := by
  rw [← trace_mul_star, ← trace_mul_star]
  rw [mul_assoc, TrivialExtension.trace_mul_comm]

theorem tensorRightCoordinates_left (a : R) (x : R ⊗[k] R) (i : TIndex) :
    tensorRightCoordinates q (AbsoluteBar.left k R 1 a x) i =
      a * tensorRightCoordinates q x i := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, mul_add, hx, hy]
  | tmul b c =>
    change tensorRightCoordinates q ((a * b) ⊗ₜ[k] c) i = _
    simp only [tensorRightCoordinates_tmul, Algebra.mul_smul_comm]

theorem twistedCasimir_equivariant (H : kˣ) (a : R) :
    AbsoluteBar.left k R 1 (TrivialExtension.twist H a) (twistedCasimir q H) =
      AbsoluteBar.right k R 1 (MulOpposite.op a) (twistedCasimir q H) := by
  apply (tensorRightCoordinates q).injective
  funext i
  rw [tensorRightCoordinates_left, twistedCasimir_coordinates, ← map_mul]
  simp only [twistedCasimir, map_sum, AbsoluteBar.right_tmul k R 0, AbsoluteBar.right_zero k R, MulOpposite.unop_op, Finset.sum_apply,
    tensorRightCoordinates_tmul, coefficient_right_product]
  have he := congrArg (TrivialExtension.twist H) (expand q (a * vector q i.star))
  simpa only [map_sum, map_smul] using he

end ArExplicit.T

end

end OAI
