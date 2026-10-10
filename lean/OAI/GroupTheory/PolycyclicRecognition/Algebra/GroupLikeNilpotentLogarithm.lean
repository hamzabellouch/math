import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommutingUnipotentLogarithm
import Mathlib.RingTheory.TensorProduct.Basic

namespace OAI

/-! # The logarithm of a unipotent group-like element is primitive -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Algebra ℚ A]

theorem nilpotentLog_groupLike
    (Δ : A →ₐ[R] A ⊗[R] A) (a : A) (ha : IsNilpotent a)
    (hΔ : Δ (1 + a) = (1 + a) ⊗ₜ[R] (1 + a)) :
    Δ (nilpotentLog a) =
      nilpotentLog a ⊗ₜ[R] (1 : A) + (1 : A) ⊗ₜ[R] nilpotentLog a := by
  let l : A →+* A ⊗[R] A := Algebra.TensorProduct.includeLeftRingHom
  let r : A →+* A ⊗[R] A := Algebra.TensorProduct.includeRight.toRingHom
  have hl (x : A) : l x = x ⊗ₜ[R] (1 : A) := rfl
  have hr (x : A) : r x = (1 : A) ⊗ₜ[R] x := rfl
  have hc : Commute (l a) (r a) := by
    change Commute (a ⊗ₜ[R] (1 : A)) ((1 : A) ⊗ₜ[R] a)
    change (a ⊗ₜ[R] (1 : A)) * ((1 : A) ⊗ₜ[R] a) =
      ((1 : A) ⊗ₜ[R] a) * (a ⊗ₜ[R] (1 : A))
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hf : (1 + a) ⊗ₜ[R] (1 + a) = (1 + l a) * (1 + r a) := by
    simp only [hl, hr, add_tmul, tmul_add, add_mul, mul_add, one_mul, mul_one,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.one_def]
  have hd : Δ a = (1 + l a) * (1 + r a) - 1 := by
    rw [← hf, ← hΔ, map_add, map_one, add_sub_cancel_left]
  change Δ.toRingHom (nilpotentLog a) = _
  rw [← nilpotentLog_map Δ.toRingHom a ha]
  change nilpotentLog (Δ a) = _
  rw [hd, nilpotentLog_unipotent_mul hc (ha.map l) (ha.map r),
    nilpotentLog_map l a ha, nilpotentLog_map r a ha, hl, hr]

end PolycyclicRecognition

end

end OAI
