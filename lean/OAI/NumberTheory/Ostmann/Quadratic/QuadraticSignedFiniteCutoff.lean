import OAI.NumberTheory.Ostmann.Quadratic.QuadraticOddKernelCutoff
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSignedKernelTail

namespace OAI

/-! # Exact finite kernel truncation of the signed frequency expansion -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_signed_low_sum (F : ℤ → ℂ) (hF : Summable (fun h => ‖F h‖)) (K : ℕ) :
    (∑' z : QuadraticFrequencyIndex,
      if (z.2.1.val : ℕ) ≤ K then F (quadraticFrequencyValue z) else 0) =
    ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ), ∑ b ∈ oddSquarefreeRange K,
      ∑' c : ℕ+, F (a * (c : ℕ) ^ 2 * b) := by
  have hindex := hF.comp_injective quadraticFrequencyValue_injective
  have hlow : Summable (fun z : QuadraticFrequencyIndex =>
      if (z.2.1.val : ℕ) ≤ K then F (quadraticFrequencyValue z) else 0) := by
    apply Summable.of_norm_bounded hindex
    intro z
    split_ifs <;> simp
  rw [hlow.tsum_prod]
  have ha (a : ({1, -1, 2, -2} : Finset ℤ)) :
      (∑' bc : QuadraticOddKernel × ℕ+,
        if (bc.1.val : ℕ) ≤ K then F (quadraticFrequencyValue (a, bc)) else 0) =
        ∑ b ∈ oddSquarefreeRange K, ∑' c : ℕ+, F ((a : ℤ) * (c : ℕ) ^ 2 * b) := by
    rw [(hlow.prod_factor a).tsum_prod]
    have hb (b : QuadraticOddKernel) :
        (∑' c : ℕ+, if (b.val : ℕ) ≤ K then F (quadraticFrequencyValue (a, (b, c))) else 0) =
        if (b.val : ℕ) ≤ K then (∑' c : ℕ+, F ((a : ℤ) * (c : ℕ) ^ 2 * (b.val : ℕ))) else 0 := by
      by_cases h : (b.val : ℕ) ≤ K
      · simp only [h, ite_true, quadraticFrequencyValue]
      · simp only [h, ite_false, tsum_zero]
    simp_rw [hb]
    exact quadratic_odd_kernel_cutoff K (fun b => ∑' c : ℕ+, F ((a : ℤ) * (c : ℕ) ^ 2 * b))
  simp_rw [ha]
  exact Finset.tsum_subtype ({1, -1, 2, -2} : Finset ℤ)
    (fun a : ℤ => ∑ b ∈ oddSquarefreeRange K, ∑' c : ℕ+, F (a * (c : ℕ) ^ 2 * b))

theorem quadratic_signed_finite_cutoff (F : ℤ → ℂ) (hzero : F 0 = 0)
    (hF : Summable (fun h => ‖F h‖)) (K : ℕ) :
    (∑' h : ℤ, F h) =
      (∑ a ∈ ({1, -1, 2, -2} : Finset ℤ), ∑ b ∈ oddSquarefreeRange K,
        ∑' c : ℕ+, F (a * (c : ℕ) ^ 2 * b)) +
      ∑' z : QuadraticFrequencyIndex,
        if K < (z.2.1.val : ℕ) then F (quadraticFrequencyValue z) else 0 := by
  have hindex := hF.comp_injective quadraticFrequencyValue_injective
  have hlow : Summable (fun z : QuadraticFrequencyIndex =>
      if (z.2.1.val : ℕ) ≤ K then F (quadraticFrequencyValue z) else 0) := by
    apply Summable.of_norm_bounded hindex
    intro z
    split_ifs <;> simp
  have hhigh : Summable (fun z : QuadraticFrequencyIndex =>
      if K < (z.2.1.val : ℕ) then F (quadraticFrequencyValue z) else 0) := by
    apply Summable.of_norm_bounded hindex
    intro z
    split_ifs <;> simp
  rw [quadratic_signed_tsum F hzero, ← quadratic_signed_low_sum F hF K,
    ← hlow.tsum_add hhigh]
  apply tsum_congr
  intro z
  by_cases h : (z.2.1.val : ℕ) ≤ K
  · simp only [h, not_lt.mpr h, ite_true, ite_false, add_zero]
  · simp only [h, lt_of_not_ge h, ite_false, ite_true, zero_add]

end Ostmann

end OAI
