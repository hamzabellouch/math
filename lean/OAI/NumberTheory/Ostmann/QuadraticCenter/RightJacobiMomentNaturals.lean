import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiMomentFamily
import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiMomentReindex

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

private theorem union_primeFactors_prime (S : Finset ℕ) :
    ∀ p ∈ S.biUnion Nat.primeFactors, Nat.Prime p := by
  intro p hp
  obtain ⟨n, hn, hp⟩ := Finset.mem_biUnion.mp hp
  exact (Nat.mem_primeFactors.mp hp).1

private theorem primeFactors_subset_union (S : Finset ℕ) :
    ∀ n ∈ S, n.primeFactors ⊆ S.biUnion Nat.primeFactors := by
  intro n hn p hp
  exact Finset.mem_biUnion.mpr ⟨n, hn, hp⟩

private theorem liftSquarefreeArray_cutoff (P S : Finset ℕ) (b : ℕ → ℂ) (B : ℕ)
    (hB : ∀ n ∈ S, n ≤ B) :
    ∀ s, B < primeSubsetProduct s → liftSquarefreeArray P S b s = 0 := by
  intro s hs
  have hn : primeSubsetProduct s ∉ S := fun hn =>
    (not_lt_of_ge (hB _ hn)) hs
  simp only [liftSquarefreeArray, ite_eq_right hn]

theorem squarefree_jacobi_complex_moment_le (S : Finset ℕ)
    (hS : ∀ n ∈ S, Squarefree n) (b : ℕ → ℂ) (B N : ℕ)
    (hB : ∀ n ∈ S, n ≤ B) {l : ℕ} (hl : 1 ≤ l) :
    (∑ m ∈ (Finset.range N).filter Odd,
      ‖∑ n ∈ S, b n * (jacobiSym (n : ℤ) m : ℂ)‖ ^ (2 * l)) ≤
      (2 : ℝ) ^ l *
        ((N : ℝ) *
          (∑ n ∈ S, ((((2 * l : ℕ) : ℝ) ^ 2) ^ n.primeFactors.card) * ‖b n‖ ^ 2) ^ l +
          (4 * (B : ℝ) ^ (2 * l)) * (∑ n ∈ S, ‖b n‖) ^ (2 * l)) := by
  classical
  let P := S.biUnion Nat.primeFactors
  have hP := union_primeFactors_prime S
  have hc := primeFactors_subset_union S
  have ht := actual_jacobi_complex_moment_le hP (liftSquarefreeArray P S b) B N
    (liftSquarefreeArray_cutoff P S b B hB) hl
  have heq (m : ℕ) := sum_liftSquarefreeArray_mul hP S hS hc b
    (fun n => (jacobiSym (n : ℤ) m : ℂ))
  dsimp only [P] at ht
  simpa only [heq, sum_liftSquarefreeArray_energy hP S hS hc b,
    sum_liftSquarefreeArray_norm hP S hS hc b] using ht

theorem squarefree_jacobi_complex_family_moment_le (S : Finset ℕ)
    (hS : ∀ n ∈ S, Squarefree n) {α : Type*} (F : Finset α) (hF : F.Nonempty)
    (b : α → ℕ → ℂ) (B N : ℕ) (hB : ∀ n ∈ S, n ≤ B)
    {l : ℕ} (hl : 1 ≤ l) :
    (∑ m ∈ (Finset.range N).filter Odd,
      (F.sup' hF (fun a => ‖∑ n ∈ S, b a n * (jacobiSym (n : ℤ) m : ℂ)‖)) ^ (2 * l)) ≤
      (2 : ℝ) ^ l * ∑ a ∈ F,
        ((N : ℝ) *
          (∑ n ∈ S, ((((2 * l : ℕ) : ℝ) ^ 2) ^ n.primeFactors.card) * ‖b a n‖ ^ 2) ^ l +
          (4 * (B : ℝ) ^ (2 * l)) * (∑ n ∈ S, ‖b a n‖) ^ (2 * l)) := by
  classical
  let P := S.biUnion Nat.primeFactors
  have hP := union_primeFactors_prime S
  have hc := primeFactors_subset_union S
  have ht := actual_jacobi_complex_family_moment_le hP F hF
    (fun a => liftSquarefreeArray P S (b a)) B N
    (fun a ha => liftSquarefreeArray_cutoff P S (b a) B hB) hl
  have heq (a : α) (m : ℕ) := sum_liftSquarefreeArray_mul hP S hS hc (b a)
    (fun n => (jacobiSym (n : ℤ) m : ℂ))
  dsimp only [P] at ht
  simpa only [heq, sum_liftSquarefreeArray_energy hP S hS hc,
    sum_liftSquarefreeArray_norm hP S hS hc] using ht

theorem squarefree_jacobi_complex_family_moment_le_card (S : Finset ℕ)
    (hS : ∀ n ∈ S, Squarefree n) {α : Type*} (F : Finset α) (hF : F.Nonempty)
    (b : α → ℕ → ℂ) (B N : ℕ) (hB : ∀ n ∈ S, n ≤ B)
    {l : ℕ} (hl : 1 ≤ l) (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (henergy : ∀ a ∈ F,
      (∑ n ∈ S, ((((2 * l : ℕ) : ℝ) ^ 2) ^ n.primeFactors.card) * ‖b a n‖ ^ 2) ≤ U)
    (hmass : ∀ a ∈ F, (∑ n ∈ S, ‖b a n‖) ≤ V) :
    (∑ m ∈ (Finset.range N).filter Odd,
      (F.sup' hF (fun a => ‖∑ n ∈ S, b a n * (jacobiSym (n : ℤ) m : ℂ)‖)) ^ (2 * l)) ≤
      (F.card : ℝ) * (2 : ℝ) ^ l *
        ((N : ℝ) * U ^ l + (4 * (B : ℝ) ^ (2 * l)) * V ^ (2 * l)) := by
  classical
  let P := S.biUnion Nat.primeFactors
  have hP := union_primeFactors_prime S
  have hc := primeFactors_subset_union S
  have he : ∀ a ∈ F,
      (∑ s, ((((2 * l : ℕ) : ℝ) ^ 2) ^ s.card) *
        ‖liftSquarefreeArray P S (b a) s‖ ^ 2) ≤ U := by
    intro a ha
    rw [sum_liftSquarefreeArray_energy hP S hS hc]
    exact henergy a ha
  have hm : ∀ a ∈ F, (∑ s, ‖liftSquarefreeArray P S (b a) s‖) ≤ V := by
    intro a ha
    rw [sum_liftSquarefreeArray_norm hP S hS hc]
    exact hmass a ha
  have ht := actual_jacobi_complex_family_moment_le_card hP F hF
    (fun a => liftSquarefreeArray P S (b a)) B N
    (fun a ha => liftSquarefreeArray_cutoff P S (b a) B hB) hl U V hU hV he hm
  have heq (a : α) (m : ℕ) := sum_liftSquarefreeArray_mul hP S hS hc (b a)
    (fun n => (jacobiSym (n : ℤ) m : ℂ))
  dsimp only [P] at ht
  simpa only [heq] using ht

end Ostmann.QuadraticCenter

end OAI
