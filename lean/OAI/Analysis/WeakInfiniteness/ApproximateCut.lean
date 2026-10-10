import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

section Ordered

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma norm_sub_mul_of_pos_contraction (x y : A) (hy : 0 ≤ y) (hyn : ‖y‖ ≤ 1) :
    ‖x - x * y‖ ≤ ‖x‖ := by
  have hy' : 0 ≤ (y : Unitization ℂ A) := Unitization.inr_nonneg_iff.mpr hy
  have hyp : (y : Unitization ℂ A) ≤ 1 :=
    (norm_le_one_iff_of_nonneg _ hy').mp (by simpa only [Unitization.norm_inr] using hyn)
  have hn : ‖(1 : Unitization ℂ A) - y‖ ≤ 1 :=
    (norm_le_one_iff_of_nonneg _ (sub_nonneg.mpr hyp)).mpr (by simpa using hy')
  calc
    ‖x - x * y‖ = ‖(x : Unitization ℂ A) * (1 - y)‖ := by
      rw [mul_sub, mul_one, ← Unitization.inr_mul, ← Unitization.inr_sub, Unitization.norm_inr]
    _ ≤ ‖(x : Unitization ℂ A)‖ * ‖(1 : Unitization ℂ A) - y‖ := norm_mul_le _ _
    _ ≤ ‖(x : Unitization ℂ A)‖ * 1 := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = ‖x‖ := by rw [mul_one,Unitization.norm_inr]

end Ordered

end WeakPureInfiniteness
end

end OAI
