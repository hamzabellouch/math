import OAI.NumberTheory.Ostmann.Characters.SquarefreeBonami

namespace OAI

/-! # Exact moments of the Boolean monomials -/

namespace Ostmann

open scoped BigOperators

def monomialOccurrence {ι : Type*} [Fintype ι] {P : Finset ℕ}
    (σ : ι → Finset P) (p : P) : ℕ :=
  (Finset.univ.filter (fun i => p ∈ σ i)).card

theorem rademacherMonomial_univ {P : Finset ℕ} (Q : Finset P) (ε : P → Bool) :
    rademacherMonomial Q ε = ∏ p : P, if p ∈ Q then (if ε p then 1 else -1 : ℝ) else 1 := by
  classical
  exact (Finset.prod_ite_mem_eq Q (fun p => if ε p then (1 : ℝ) else -1)).symm

theorem rademacherMonomial_product {ι : Type*} [Fintype ι] {P : Finset ℕ}
    (σ : ι → Finset P) (ε : P → Bool) :
    (∏ i, rademacherMonomial (σ i) ε) =
      ∏ p : P, (if ε p then (1 : ℝ) else -1) ^ monomialOccurrence σ p := by
  classical
  simp_rw [rademacherMonomial_univ]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const, monomialOccurrence]

private theorem bool_sign_power_sum (n : ℕ) :
    (∑ b : Bool, (if b then (1 : ℝ) else -1) ^ n) = if Even n then 2 else 0 := by
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, ite_false, ite_true, one_pow, neg_one_pow_eq_ite]
  split_ifs <;> norm_num

theorem rademacher_product_average {ι : Type*} [Fintype ι] (P : Finset ℕ)
    (σ : ι → Finset P) :
    (Fintype.card (P → Bool) : ℝ)⁻¹ *
      ∑ ε : P → Bool, ∏ i, rademacherMonomial (σ i) ε =
        if ∀ p : P, Even (monomialOccurrence σ p) then 1 else 0 := by
  classical
  simp_rw [rademacherMonomial_product]
  rw [← Fintype.prod_sum (fun (p : P) (b : Bool) =>
    (if b then (1 : ℝ) else -1) ^ monomialOccurrence σ p)]
  simp_rw [bool_sign_power_sum]
  by_cases h : ∀ p : P, Even (monomialOccurrence σ p)
  · simp only [h, ite_true, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    have hcard : Fintype.card (P → Bool) = 2 ^ P.card := by simp
    rw [hcard, Nat.cast_pow, Nat.cast_ofNat, inv_mul_cancel₀ (by positivity)]
    simp
  · obtain ⟨p, hp⟩ := not_forall.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ p) (by simp [hp]), mul_zero, ite_eq_right h]

theorem rademacher_even_moment {ι : Type*} [Fintype ι] (P : Finset ℕ)
    (σ : ι → Finset P) (a : ι → ℝ) (l : ℕ) :
    (Fintype.card (P → Bool) : ℝ)⁻¹ *
      ∑ ε : P → Bool, |∑ i, a i * rademacherMonomial (σ i) ε| ^ (2 * l) =
      ∑ t : Fin (2 * l) → ι,
        (∏ j, a (t j)) * (if ∀ p : P, Even (monomialOccurrence (fun j => σ (t j)) p) then 1 else 0) := by
  classical
  simp only [Even.pow_abs (even_two_mul l)]
  simp_rw [Fintype.sum_pow, Finset.prod_mul_distrib]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.mul_sum, mul_left_comm, rademacher_product_average]

end Ostmann

end OAI
