import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiMoment

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem actual_jacobi_complex_family_moment_le {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) {α : Type*} (F : Finset α) (hF : F.Nonempty)
    (b : α → Finset P → ℂ) (B N : ℕ)
    (hb : ∀ a ∈ F, ∀ s, B < primeSubsetProduct s → b a s = 0)
    {l : ℕ} (hl : 1 ≤ l) :
    (∑ m ∈ (Finset.range N).filter Odd,
      (F.sup' hF (fun a =>
        ‖∑ s, b a s * (jacobiSym (primeSubsetProduct s : ℤ) m : ℂ)‖)) ^ (2 * l)) ≤
      (2 : ℝ) ^ l * ∑ a ∈ F,
        ((N : ℝ) * (∑ s, ((((2 * l : ℕ) : ℝ) ^ 2) ^ s.card) * ‖b a s‖ ^ 2) ^ l +
          (4 * (B : ℝ) ^ (2 * l)) * (∑ s, ‖b a s‖) ^ (2 * l)) := by
  classical
  calc
    _ ≤ ∑ m ∈ (Finset.range N).filter Odd, ∑ a ∈ F,
        ‖∑ s, b a s * (jacobiSym (primeSubsetProduct s : ℤ) m : ℂ)‖ ^ (2 * l) := by
      apply Finset.sum_le_sum
      intro m hm
      obtain ⟨a, ha, heq⟩ := F.exists_mem_eq_sup' hF
        (fun a => ‖∑ s, b a s * (jacobiSym (primeSubsetProduct s : ℤ) m : ℂ)‖)
      rw [heq]
      exact Finset.single_le_sum
        (f := fun a => ‖∑ s, b a s * (jacobiSym (primeSubsetProduct s : ℤ) m : ℂ)‖ ^ (2 * l))
        (fun i hi => by positivity) ha
    _ = ∑ a ∈ F, ∑ m ∈ (Finset.range N).filter Odd,
        ‖∑ s, b a s * (jacobiSym (primeSubsetProduct s : ℤ) m : ℂ)‖ ^ (2 * l) :=
      Finset.sum_comm
    _ ≤ _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun a ha =>
        actual_jacobi_complex_moment_le hP (b a) B N (hb a ha) hl)

theorem actual_jacobi_complex_family_moment_le_card {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) {α : Type*} (F : Finset α) (hF : F.Nonempty)
    (b : α → Finset P → ℂ) (B N : ℕ)
    (hb : ∀ a ∈ F, ∀ s, B < primeSubsetProduct s → b a s = 0)
    {l : ℕ} (hl : 1 ≤ l) (U V : ℝ) (_hU : 0 ≤ U) (_hV : 0 ≤ V)
    (henergy : ∀ a ∈ F,
      (∑ s, ((((2 * l : ℕ) : ℝ) ^ 2) ^ s.card) * ‖b a s‖ ^ 2) ≤ U)
    (hmass : ∀ a ∈ F, (∑ s, ‖b a s‖) ≤ V) :
    (∑ m ∈ (Finset.range N).filter Odd,
      (F.sup' hF (fun a =>
        ‖∑ s, b a s * (jacobiSym (primeSubsetProduct s : ℤ) m : ℂ)‖)) ^ (2 * l)) ≤
      (F.card : ℝ) * (2 : ℝ) ^ l *
        ((N : ℝ) * U ^ l + (4 * (B : ℝ) ^ (2 * l)) * V ^ (2 * l)) := by
  classical
  apply (actual_jacobi_complex_family_moment_le hP F hF b B N hb hl).trans
  calc
    _ ≤ (2 : ℝ) ^ l * ∑ _a ∈ F,
        ((N : ℝ) * U ^ l + (4 * (B : ℝ) ^ (2 * l)) * V ^ (2 * l)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro a ha
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (Finset.sum_nonneg (fun s hs => by positivity))
          (henergy a ha) l
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (Finset.sum_nonneg (fun s hs => norm_nonneg _))
          (hmass a ha) (2 * l)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end Ostmann.QuadraticCenter

end OAI
