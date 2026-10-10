import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductSampling

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem primeProduct_family_moment_le {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (ho : ∀ p ∈ P, Odd p)
    {H k : ℕ} (hH : ∀ p ∈ P, p ≤ H)
    (S : Finset ℕ) (hS : ∀ n ∈ S, Squarefree n)
    {α : Type*} (F : Finset α) (hF : F.Nonempty)
    (b : α → ℕ → ℂ) (B : ℕ) (hB : ∀ n ∈ S, n ≤ B)
    {l : ℕ} (hl : 1 ≤ l) (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (henergy : ∀ a ∈ F,
      (∑ n ∈ S, ((((2 * l : ℕ) : ℝ) ^ 2) ^ n.primeFactors.card) * ‖b a n‖ ^ 2) ≤ U)
    (hmass : ∀ a ∈ F, (∑ n ∈ S, ‖b a n‖) ≤ V) :
    primeProductMean P k (fun m =>
      (F.sup' hF (fun a => ‖∑ n ∈ S, b a n * (jacobiSym (n : ℤ) m : ℂ)‖)) ^ (2 * l)) ≤
      ((F.card : ℝ) * (2 : ℝ) ^ l *
        (((H ^ k + 1 : ℕ) : ℝ) * U ^ l + (4 * (B : ℝ) ^ (2 * l)) * V ^ (2 * l))) /
        (Nat.choose P.card k : ℝ) := by
  have hn (m : ℕ) : 0 ≤
      (F.sup' hF (fun a => ‖∑ n ∈ S, b a n * (jacobiSym (n : ℤ) m : ℂ)‖)) ^ (2 * l) := by
    obtain ⟨a, ha, he⟩ := F.exists_mem_eq_sup' hF
      (fun a => ‖∑ n ∈ S, b a n * (jacobiSym (n : ℤ) m : ℂ)‖)
    rw [he]
    positivity
  apply (primeProductMean_le_odd_sum hP ho hH _ hn).trans
  exact div_le_div_of_nonneg_right
    (squarefree_jacobi_complex_family_moment_le_card S hS F hF b B (H ^ k + 1)
      hB hl U V hU hV henergy hmass) (Nat.cast_nonneg _)

theorem primeProduct_probability_le {P : Finset ℕ} {k : ℕ}
    (hJ : 0 < P.card) (hk : 2 * k ≤ P.card) :
    (Nat.choose P.card k : ℝ)⁻¹ ≤ (k.factorial : ℝ) * (2 / (P.card : ℝ)) ^ k := by
  have hJr : (0 : ℝ) < P.card := by exact_mod_cast hJ
  have hkJ : k ≤ P.card := by omega
  have hchoose : (0 : ℝ) < Nat.choose P.card k := by exact_mod_cast Nat.choose_pos hkJ
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hb := half_card_pow_le_choose hk
  have hleft : 0 < ((P.card : ℝ) / 2) ^ k / k.factorial := by positivity
  have hi := one_div_le_one_div_of_le hleft hb
  calc
    _ ≤ 1 / (((P.card : ℝ) / 2) ^ k / k.factorial) := by simpa only [one_div] using hi
    _ = _ := by
      simp only [div_pow]
      field_simp

theorem primeProduct_family_moment_le_factorial {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (ho : ∀ p ∈ P, Odd p)
    (hJ : 0 < P.card) {H k : ℕ} (hk : 2 * k ≤ P.card) (hH : ∀ p ∈ P, p ≤ H)
    (S : Finset ℕ) (hS : ∀ n ∈ S, Squarefree n)
    {α : Type*} (F : Finset α) (hF : F.Nonempty)
    (b : α → ℕ → ℂ) (B : ℕ) (hB : ∀ n ∈ S, n ≤ B)
    {l : ℕ} (hl : 1 ≤ l) (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (henergy : ∀ a ∈ F,
      (∑ n ∈ S, ((((2 * l : ℕ) : ℝ) ^ 2) ^ n.primeFactors.card) * ‖b a n‖ ^ 2) ≤ U)
    (hmass : ∀ a ∈ F, (∑ n ∈ S, ‖b a n‖) ≤ V) :
    primeProductMean P k (fun m =>
      (F.sup' hF (fun a => ‖∑ n ∈ S, b a n * (jacobiSym (n : ℤ) m : ℂ)‖)) ^ (2 * l)) ≤
      ((F.card : ℝ) * (2 : ℝ) ^ l *
        (((H ^ k + 1 : ℕ) : ℝ) * U ^ l + (4 * (B : ℝ) ^ (2 * l)) * V ^ (2 * l))) *
        ((k.factorial : ℝ) * (2 / (P.card : ℝ)) ^ k) := by
  apply (primeProduct_family_moment_le hP ho hH S hS F hF b B hB hl U V hU hV henergy hmass).trans
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (primeProduct_probability_le hJ hk) (by positivity)

end Ostmann.QuadraticCenter

end

end OAI
