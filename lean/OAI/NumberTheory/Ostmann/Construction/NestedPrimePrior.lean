import OAI.NumberTheory.Ostmann.Construction.InitialPrimePrior

namespace OAI

/-! # Returning to an initial law that already excludes prescribed primes -/

namespace Ostmann
open scoped Classical BigOperators

/-- Global exclusions made when constructing the word remain excluded.
Only the extra, nonbulk-dependent deletion is undone. The error can still
be charged to the larger shell and its conditional normalizer. -/
theorem nested_prime_prior_bound {J : Type*} [Fintype J]
    (P : Finset ℕ) (S initial D : J → Finset ℕ) (hSP : ∀ j, S j ⊆ P)
    (hsub : ∀ j, initial j ⊆ S j) (hretain : ∀ j, S j \ D j ⊆ initial j)
    (hnew : ∀ j, 0 < ∑ q ∈ S j \ D j, (q : ℝ)⁻¹)
    (F : (J → P) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖∑ x, ((∏ j, primeSubsetPrior P (initial j) (x j) : ℝ) : ℂ) * F x‖ ≤
      ‖∑ x, ((∏ j, primeSubsetPrior P (S j \ D j) (x j) : ℝ) : ℂ) * F x‖ +
        B * ((∏ j, (1 + (∑ q ∈ S j \ D j, (q : ℝ)⁻¹)⁻¹ *
          ∑ q ∈ S j ∩ D j, (q : ℝ)⁻¹)) - 1) := by
  have heq (j) : initial j \ D j = S j \ D j := by
    ext q
    constructor
    · intro hq
      exact Finset.mem_sdiff.mpr ⟨hsub j (Finset.mem_sdiff.mp hq).1, (Finset.mem_sdiff.mp hq).2⟩
    · intro hq
      exact Finset.mem_sdiff.mpr ⟨hretain j hq, (Finset.mem_sdiff.mp hq).2⟩
  have hb := initial_prime_prior_bound P initial D (fun j => (hsub j).trans (hSP j))
    (fun j => by simpa only [heq] using hnew j) F B hF
  dsimp only at hb
  simp_rw [heq] at hb
  apply hb.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ hB
  apply sub_le_sub_right
  apply Finset.prod_le_prod₀
  · intro j _
    have hmass : 0 ≤ ∑ q ∈ initial j ∩ D j, (q : ℝ)⁻¹ :=
      Finset.sum_nonneg fun q _ => inv_nonneg.mpr (Nat.cast_nonneg q)
    positivity
  · intro j _
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hnew j).le)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      exact Finset.mem_inter.mpr ⟨hsub j (Finset.mem_inter.mp hq).1, (Finset.mem_inter.mp hq).2⟩
    · intros
      positivity

/-- The initial law may retain any prescribed global exclusions between the
full shell and the additionally conditioned law. -/
theorem nested_prime_prior_three_errors {J : Type*} [Fintype J]
    (P : Finset ℕ) (S initial D : J → Finset ℕ) (hSP : ∀ j, S j ⊆ P)
    (hsub : ∀ j, initial j ⊆ S j) (hretain : ∀ j, S j \ D j ⊆ initial j)
    (hnew : ∀ j, 0 < ∑ q ∈ S j \ D j, (q : ℝ)⁻¹)
    (F : (J → P) → ℂ) (B main error tail : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B)
    (hmean : ‖∑ x, ((∏ j, primeSubsetPrior P (S j \ D j) (x j) : ℝ) : ℂ) * F x‖ ≤
      main + error + tail)
    (herror : B * ((∏ j, (1 + (∑ q ∈ S j \ D j, (q : ℝ)⁻¹)⁻¹ *
      ∑ q ∈ S j ∩ D j, (q : ℝ)⁻¹)) - 1) ≤ tail) :
    ‖∑ x, ((∏ j, primeSubsetPrior P (initial j) (x j) : ℝ) : ℂ) * F x‖ ≤
      main + error + 2 * tail := by
  apply (nested_prime_prior_bound P S initial D hSP hsub hretain hnew F B hB hF).trans
  exact (add_le_add hmean herror).trans_eq (by ring)

end Ostmann

end OAI
