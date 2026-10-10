import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDyadicDivisors

namespace OAI

/-! # Selecting a genuine divisor block with the original product range -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticDyadicDivisorMass (M N₁ N₂ D i j : ℕ) (a b : ℕ → ℂ) : ℝ :=
  ∑ s ∈ quadraticDyadicDivisors N₁ i, ∑ t ∈ quadraticDyadicDivisors N₂ j,
    if D < s * t ∧ s * t ≤ 2 * D then
      ∑ m ∈ oddSquarefreeRange M, ‖quadraticCoprimeBilinear N₁ N₂
        (fun n => if s ∣ n then a n else 0)
        (fun n => if t ∣ n then b n else 0) m‖ else 0

 theorem quadraticDyadicDivisorMass_nonneg (M N₁ N₂ D i j : ℕ) (a b : ℕ → ℂ) :
    0 ≤ quadraticDyadicDivisorMass M N₁ N₂ D i j a b := by
  apply Finset.sum_nonneg
  intro s _
  apply Finset.sum_nonneg
  intro t _
  split_ifs
  · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  · rfl

 theorem quadratic_dyadic_divisor_mass_total (M N₁ N₂ D : ℕ) (a b : ℕ → ℂ) :
    (∑ i ∈ Finset.range (Nat.log 2 N₁ + 1), ∑ j ∈ Finset.range (Nat.log 2 N₂ + 1),
      quadraticDyadicDivisorMass M N₁ N₂ D i j a b) =
      ∑ z ∈ quadraticDivisorRangePairs N₁ N₂ D, ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticCoprimeBilinear N₁ N₂
          (fun n => if z.1 ∣ n then a n else 0)
          (fun n => if z.2 ∣ n then b n else 0) m‖ := by
  unfold quadraticDyadicDivisorMass
  rw [quadratic_dyadic_pair_sum]
  rw [quadraticDivisorRangePairs, Finset.sum_filter, Finset.product_eq_sprod,
    Finset.sum_product]

 theorem quadratic_positive_block_product_bounds {M N₁ N₂ D i j : ℕ} (a b : ℕ → ℂ)
    (h : 0 < quadraticDyadicDivisorMass M N₁ N₂ D i j a b) :
    D < 4 * (2 ^ i * 2 ^ j) ∧ 2 ^ i * 2 ^ j ≤ 2 * D := by
  have hw (s t : ℕ) : 0 ≤
      (if D < s * t ∧ s * t ≤ 2 * D then
        ∑ m ∈ oddSquarefreeRange M, ‖quadraticCoprimeBilinear N₁ N₂
          (fun n => if s ∣ n then a n else 0)
          (fun n => if t ∣ n then b n else 0) m‖ else 0) := by
    split_ifs
    · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    · rfl
  obtain ⟨s, hs, hsum⟩ := (Finset.sum_pos_iff_of_nonneg (fun s _ =>
    Finset.sum_nonneg (fun t _ => hw s t))).mp h
  obtain ⟨t, ht, hp⟩ := (Finset.sum_pos_iff_of_nonneg (fun t _ => hw s t)).mp hsum
  have hd : D < s * t ∧ s * t ≤ 2 * D := by
    by_contra hd
    simp only [ite_eq_right hd, lt_self_iff_false] at hp
  obtain ⟨hsl, hsu⟩ := quadraticDyadicDivisors_bounds hs
  obtain ⟨htl, htu⟩ := quadraticDyadicDivisors_bounds ht
  have hlo := Nat.mul_le_mul hsl htl
  have hhi := Nat.mul_lt_mul_of_lt_of_lt hsu htu
  rw [pow_succ, pow_succ] at hhi
  constructor
  · nlinarith [hd.1]
  · exact hlo.trans hd.2

 theorem quadratic_divisor_block_selection (M N₁ N₂ D : ℕ) (a b : ℕ → ℂ)
    (hpos : 0 < ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) :
    ∃ i ≤ Nat.log 2 N₁, ∃ j ≤ Nat.log 2 N₂,
      0 < quadraticDyadicDivisorMass M N₁ N₂ D i j a b ∧
      D < 4 * (2 ^ i * 2 ^ j) ∧ 2 ^ i * 2 ^ j ≤ 2 * D ∧
      (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
      ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) *
        quadraticDyadicDivisorMass M N₁ N₂ D i j a b := by
  let J := (Finset.range (Nat.log 2 N₁ + 1)).product (Finset.range (Nat.log 2 N₂ + 1))
  let F : ℕ × ℕ → ℝ := fun z => quadraticDyadicDivisorMass M N₁ N₂ D z.1 z.2 a b
  have hJ : J.Nonempty := ⟨(0, 0), Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image J F hJ
  have hsum : (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
      ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) * F z := by
    calc
      _ ≤ ∑ w ∈ J, F w := by
        rw [show J = (Finset.range (Nat.log 2 N₁ + 1)).product
          (Finset.range (Nat.log 2 N₂ + 1)) from rfl,
          Finset.product_eq_sprod, Finset.sum_product]
        rw [quadratic_dyadic_divisor_mass_total]
        exact quadratic_divisor_range_triangle M N₁ N₂ D a b
      _ ≤ J.card • F z := Finset.sum_le_card_nsmul J F (F z) hmax
      _ = _ := by simp [J, nsmul_eq_mul, Nat.cast_mul, mul_assoc]
  have hblock : 0 < F z := by
    by_contra! hn
    have hz' : ((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) * F z ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hn
    exact (not_lt_of_ge (hsum.trans hz')) hpos
  obtain ⟨h₁, h₂⟩ := quadratic_positive_block_product_bounds a b hblock
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hz
  exact ⟨z.1, by have := Finset.mem_range.mp hi; omega,
    z.2, by have := Finset.mem_range.mp hj; omega, hblock, h₁, h₂, hsum⟩

end Ostmann

end OAI
