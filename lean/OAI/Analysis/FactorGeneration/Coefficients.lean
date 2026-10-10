import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finsupp.Order

namespace OAI

noncomputable section

namespace Generator

/-! Coefficientwise absolute-value product comparison, retaining all convolution terms contributing to the same group element. -/
section
open scoped BigOperators
variable {G : Type*} [Monoid G]

def normCoefficients (f : MonoidAlgebra ℂ G) : MonoidAlgebra ℝ G :=
  .ofCoeff (f.coeff.mapRange (fun z => ‖z‖) norm_zero)

omit [Monoid G] in
@[simp] theorem normCoefficients_apply (f : MonoidAlgebra ℂ G) (g : G) :
    (normCoefficients f).coeff g = ‖f.coeff g‖ := rfl

omit [Monoid G] in
@[simp] theorem normCoefficients_support (f : MonoidAlgebra ℂ G) :
    (normCoefficients f).coeff.support = f.coeff.support := by
  ext g
  simp only [Finsupp.mem_support_iff, normCoefficients_apply, ne_eq, norm_eq_zero]

omit [Monoid G] in
theorem normCoefficients_nonnegative (f : MonoidAlgebra ℂ G) (g : G) :
    0 ≤ (normCoefficients f).coeff g := by
  simpa only [normCoefficients_apply] using norm_nonneg (f.coeff g)

/-- Exact source inequality |fg|(w) ≤ (|f| |g|)(w), including cancellations. -/
theorem normCoefficients_mul_le (f g : MonoidAlgebra ℂ G) (w : G) :
    (normCoefficients (f * g)).coeff w ≤
      (normCoefficients f * normCoefficients g).coeff w := by
  classical
  rw [normCoefficients_apply, MonoidAlgebra.coeff_mul, MonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum, normCoefficients_support, normCoefficients_apply]
  calc
    _ ≤ ∑ a ∈ f.coeff.support,
        ‖∑ b ∈ g.coeff.support, if a * b = w then f.coeff a * g.coeff b else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a ∈ f.coeff.support, ∑ b ∈ g.coeff.support,
        ‖if a * b = w then f.coeff a * g.coeff b else 0‖ :=
      Finset.sum_le_sum fun _ _ => norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp

/-- The corresponding additive coefficient comparison. -/
theorem normCoefficients_add_le (f g : MonoidAlgebra ℂ G) (w : G) :
    (normCoefficients (f + g)).coeff w ≤
      (normCoefficients f + normCoefficients g).coeff w :=
  by simpa only [normCoefficients_apply, MonoidAlgebra.coeff_add, Finsupp.add_apply] using
    norm_add_le (f.coeff w) (g.coeff w)

end

/-! The coefficientwise ordered ring of real finite group-ring sums.
The multiplication is actual collected convolution. -/
open scoped BigOperators
namespace CoefficientOrder
variable {G : Type*} [Monoid G]

instance coefficientPartialOrder : PartialOrder (MonoidAlgebra ℝ G) :=
  PartialOrder.lift MonoidAlgebra.coeff MonoidAlgebra.coeff_injective

omit [Monoid G] in
@[simp] theorem le_iff (f g : MonoidAlgebra ℝ G) : f ≤ g ↔ ∀ w, f.coeff w ≤ g.coeff w := Iff.rfl

instance coefficientOrderedAdd : IsOrderedAddMonoid (MonoidAlgebra ℝ G) where
  add_le_add_left _f _g h _a w := add_le_add (h w) le_rfl

instance coefficientZeroLEOne : ZeroLEOneClass (MonoidAlgebra ℝ G) where
  zero_le_one := by
    intro w
    classical
    simp only [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs <;> norm_num

theorem mul_nonnegative {f g : MonoidAlgebra ℝ G} (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f * g := by
  classical
  intro w
  rw [MonoidAlgebra.coeff_mul]
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  dsimp only
  split_ifs
  · exact mul_nonneg (hf a) (hg b)
  · exact le_refl _

theorem mul_le_left {f g : MonoidAlgebra ℝ G} (h : f ≤ g)
    (a : MonoidAlgebra ℝ G) (ha : 0 ≤ a) : a * f ≤ a * g := by
  have hd : 0 ≤ g - f := fun w => sub_nonneg.mpr (h w)
  have hm := mul_nonnegative ha hd
  rw [mul_sub] at hm
  exact fun w => sub_nonneg.mp (hm w)

theorem mul_le_right {f g : MonoidAlgebra ℝ G} (h : f ≤ g)
    (a : MonoidAlgebra ℝ G) (ha : 0 ≤ a) : f * a ≤ g * a := by
  have hd : 0 ≤ g - f := fun w => sub_nonneg.mpr (h w)
  have hm := mul_nonnegative hd ha
  rw [sub_mul] at hm
  exact fun w => sub_nonneg.mp (hm w)

instance coefficientOrderedRing : IsOrderedRing (MonoidAlgebra ℝ G) where
  mul_le_mul_of_nonneg_left := by
    intro a ha b c h
    exact mul_le_left h a ha
  mul_le_mul_of_nonneg_right := by
    intro a ha b c h
    exact mul_le_right h a ha

end CoefficientOrder

end Generator

end

end OAI
