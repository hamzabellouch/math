import Mathlib

namespace OAI

noncomputable section

namespace Foulkes.Collision
open Finset
open scoped Classical
variable {A B α : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
  [Fintype α]

def distinctSum (φ : α → A →ₐ[ℂ] B) {h : ℕ} (q : Fin h → A) : B :=
  ∑ e : Fin h ↪ α, ∏ j : Fin h, φ (e j) (q j)

omit [Fintype α] in
lemma prod_update (φ : α → A →ₐ[ℂ] B) {h : ℕ} (q : Fin h → A)
    (q₀ : A) (e : Fin h ↪ α) (r : Fin h) :
    (∏ j : Fin h, φ (e j) (Function.update q r (q₀ * q r) j)) =
      φ (e r) q₀ * ∏ j : Fin h, φ (e j) (q j) := by
  classical
  have heq (j : Fin h) : φ (e j) (Function.update q r (q₀ * q r) j) =
      (if j = r then φ (e j) q₀ else 1) * φ (e j) (q j) := by
    by_cases hj : j = r
    · subst j; simp
    · simp [hj]
  simp_rw [heq]
  rw [Finset.prod_mul_distrib]
  simp

lemma distinctSum_cons (φ : α → A →ₐ[ℂ] B) {h : ℕ} (q : Fin h → A) (q₀ : A) :
    distinctSum φ (Fin.cons q₀ q) =
      ∑ e : Fin h ↪ α, ∑ i : {i // i ∉ Set.range e},
        φ i q₀ * ∏ j : Fin h, φ (e j) (q j) := by
  classical
  rw [distinctSum, ← Equiv.sum_comp (Equiv.embeddingFinSucc h α).symm,
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro i _
  simp [Equiv.coe_embeddingFinSucc_symm, Fin.prod_univ_succ]

lemma recurrence (φ : α → A →ₐ[ℂ] B) {h : ℕ} (q : Fin h → A) (q₀ : A) :
    distinctSum φ (Fin.cons q₀ q) =
      (∑ i : α, φ i q₀) * distinctSum φ q -
        ∑ r : Fin h, distinctSum φ (Function.update q r (q₀ * q r)) := by
  classical
  have hsplit (e : Fin h ↪ α) :
      (∑ i : α, φ i q₀) =
        (∑ i : {i // i ∉ Set.range e}, φ i q₀) + ∑ r : Fin h, φ (e r) q₀ := by
    have hh := Fintype.sum_subtype_add_sum_subtype (fun i : α => i ∉ Set.range e)
      (fun i => φ i q₀)
    rw [← hh]
    congr 1
    calc
      _ = ∑ i : Set.range e, φ i q₀ :=
        Equiv.sum_comp (Equiv.subtypeEquivRight (fun _ => not_not))
          (fun i : Set.range e => φ i q₀)
      _ = _ := (Equiv.sum_comp (Equiv.ofInjective e e.injective)
        (fun i : Set.range e => φ i q₀)).symm
  rw [eq_sub_iff_add_eq, distinctSum_cons]
  simp only [distinctSum, prod_update]
  rw [Finset.sum_comm (f := fun (r : Fin h) (e : Fin h ↪ α) =>
    φ (e r) q₀ * ∏ j : Fin h, φ (e j) (q j)), ← Finset.sum_add_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [hsplit e, add_mul, Finset.sum_mul, Finset.sum_mul]

end Foulkes.Collision


noncomputable section

open scoped Classical

example : ((Tuple.sort (α := ℕᵒᵈ) ![1,7,4]) 0).val = 1 := by
  rw [← show Equiv.swap (0 : Fin 3) 2 * Equiv.swap 0 1 =
      Tuple.sort (α := ℕᵒᵈ) ![1,7,4] from Tuple.eq_sort_iff.mpr (by decide +kernel)]
  rfl
example : (Equiv.Perm.sign (Tuple.sort (α := ℕᵒᵈ) ![1,7,4]) : ℤ) = 1 := by
  rw [← show Equiv.swap (0 : Fin 3) 2 * Equiv.swap 0 1 =
      Tuple.sort (α := ℕᵒᵈ) ![1,7,4] from Tuple.eq_sort_iff.mpr (by decide +kernel)]
  norm_num [map_mul, Equiv.Perm.sign_swap]


noncomputable section

example (i b : ℕ) : i ∈ List.range' 1 b ↔ 1 ≤ i ∧ i ≤ b := by
  simp only [List.mem_range', Nat.one_mul]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    omega
  · rintro ⟨hlower, hupper⟩
    exact ⟨i - 1, by omega, by omega⟩
example {B : Type*} [Fintype B] (nu : B → ℕ) (b : B) :
    (Finsupp.equivFunOnFinite.symm nu) b = nu b := by
  rfl

end
end
end

end OAI
