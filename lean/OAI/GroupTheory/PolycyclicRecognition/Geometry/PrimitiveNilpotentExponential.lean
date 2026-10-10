import OAI.GroupTheory.PolycyclicRecognition.Algebra.GroupLikeNilpotentLogarithm

namespace OAI

/-! # Products of exponentials in the primitive tensor coproduct -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Algebra ℚ A]

theorem nilpotentExp_primitive (Δ : A →ₐ[R] A ⊗[R] A) (a : A)
    (ha : IsNilpotent a) (hΔ : Δ a = a ⊗ₜ[R] (1 : A) + (1 : A) ⊗ₜ[R] a) :
    Δ (IsNilpotent.exp a) = IsNilpotent.exp a ⊗ₜ[R] IsNilpotent.exp a := by
  let l : A →+* A ⊗[R] A := Algebra.TensorProduct.includeLeftRingHom
  let r : A →+* A ⊗[R] A := Algebra.TensorProduct.includeRight.toRingHom
  have hc : Commute (l a) (r a) := by
    change (a ⊗ₜ[R] (1 : A)) * ((1 : A) ⊗ₜ[R] a) =
      ((1 : A) ⊗ₜ[R] a) * (a ⊗ₜ[R] (1 : A))
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  change Δ.toRingHom (IsNilpotent.exp a) = _
  rw [IsNilpotent.map_exp ha]
  change IsNilpotent.exp (Δ a) = _
  rw [hΔ]
  change IsNilpotent.exp (l a + r a) = _
  rw [IsNilpotent.exp_add_of_commute hc (ha.map l) (ha.map r),
    ← IsNilpotent.map_exp ha l, ← IsNilpotent.map_exp ha r]
  change (IsNilpotent.exp a ⊗ₜ[R] (1 : A)) *
    ((1 : A) ⊗ₜ[R] IsNilpotent.exp a) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem product_nilpotentExp_primitive (Δ : A →ₐ[R] A ⊗[R] A) (L : List A)
    (hL : ∀ a ∈ L, IsNilpotent a ∧ Δ a = a ⊗ₜ[R] (1 : A) + (1 : A) ⊗ₜ[R] a) :
    Δ (L.map IsNilpotent.exp).prod =
      (L.map IsNilpotent.exp).prod ⊗ₜ[R] (L.map IsNilpotent.exp).prod := by
  induction L with
  | nil => simp [Algebra.TensorProduct.one_def]
  | cons a L ih =>
    have ha := hL a (List.mem_cons_self ..)
    have htail := ih (fun b hb => hL b (List.mem_cons_of_mem a hb))
    simp only [List.map_cons, List.prod_cons, map_mul,
      nilpotentExp_primitive Δ a ha.1 ha.2, htail, Algebra.TensorProduct.tmul_mul_tmul]

theorem log_product_nilpotentExp_primitive (Δ : A →ₐ[R] A ⊗[R] A) (L : List A)
    (hL : ∀ a ∈ L, IsNilpotent a ∧ Δ a = a ⊗ₜ[R] (1 : A) + (1 : A) ⊗ₜ[R] a)
    (hu : IsNilpotent ((L.map IsNilpotent.exp).prod - 1)) :
    Δ (nilpotentLog ((L.map IsNilpotent.exp).prod - 1)) =
      nilpotentLog ((L.map IsNilpotent.exp).prod - 1) ⊗ₜ[R] (1 : A) +
      (1 : A) ⊗ₜ[R] nilpotentLog ((L.map IsNilpotent.exp).prod - 1) := by
  apply nilpotentLog_groupLike Δ _ hu
  simpa only [add_sub_cancel] using product_nilpotentExp_primitive Δ L hL

end PolycyclicRecognition

end

end OAI
