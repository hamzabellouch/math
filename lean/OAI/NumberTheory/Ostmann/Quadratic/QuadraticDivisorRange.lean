import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDivisorRectangle

namespace OAI

/-! # Bounding the original product-divisibility sum by its exact rectangle -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticDivisorRangePairs (N₁ N₂ D : ℕ) : Finset (ℕ × ℕ) :=
  ((oddSquarefreeRange N₁).product (oddSquarefreeRange N₂)).filter
    (fun z => D < z.1 * z.2 ∧ z.1 * z.2 ≤ 2 * D)

 theorem quadratic_divisor_range_triangle (M N₁ N₂ D : ℕ) (a b : ℕ → ℂ) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
    ∑ z ∈ quadraticDivisorRangePairs N₁ N₂ D, ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticCoprimeBilinear N₁ N₂
        (fun n => if z.1 ∣ n then a n else 0)
        (fun n => if z.2 ∣ n then b n else 0) m‖ := by
  let R := (oddSquarefreeRange N₁).product (oddSquarefreeRange N₂)
  let F : ℕ × ℕ → ℝ := fun z => ∑ m ∈ oddSquarefreeRange M,
    ‖quadraticCoprimeBilinear N₁ N₂
      (fun n => if z.1 ∣ n then a n else 0)
      (fun n => if z.2 ∣ n then b n else 0) m‖
  have hp (d : ℕ) (hd : 0 < d) :
      (∑ m ∈ oddSquarefreeRange M, ‖quadraticDivisorBilinear N₁ N₂ d a b m‖) ≤
        ∑ z ∈ R, if z.1 * z.2 = d then F z else 0 := by
    calc
      _ ≤ ∑ m ∈ oddSquarefreeRange M, ∑ z ∈ R,
          if z.1 * z.2 = d then
            ‖quadraticCoprimeBilinear N₁ N₂
              (fun n => if z.1 ∣ n then a n else 0)
              (fun n => if z.2 ∣ n then b n else 0) m‖ else 0 := by
        apply Finset.sum_le_sum
        intro m _
        rw [quadratic_divisor_bilinear_rectangle N₁ N₂ d hd]
        apply (norm_sum_le _ _).trans_eq
        apply Finset.sum_congr rfl
        intro z _
        split_ifs <;> simp
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : z.1 * z.2 = d <;> simp [hz, F]
  calc
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ z ∈ R,
        if z.1 * z.2 = d then F z else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      exact hp d (lt_of_le_of_lt (Nat.zero_le D) (Finset.mem_Ioc.mp hd).1)
    _ = ∑ z ∈ R, if D < z.1 * z.2 ∧ z.1 * z.2 ≤ 2 * D then F z else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      simp only [Finset.sum_ite_eq, Finset.mem_Ioc]
    _ = _ := by rw [← Finset.sum_filter]; rfl

end Ostmann

end OAI
