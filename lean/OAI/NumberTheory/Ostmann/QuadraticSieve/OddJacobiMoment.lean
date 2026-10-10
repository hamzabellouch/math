import OAI.NumberTheory.Ostmann.Characters.PeriodicCharacterSum

namespace OAI

/-! # An explicit Bonami moment bound over all odd moduli -/

namespace Ostmann

open scoped BigOperators

/-- The nonsquare contribution is bounded by `8*U^(2*l)` independently of
how many moduli are summed. Only the classical Bonami input remains. -/
theorem odd_jacobi_even_moment_bound (hB : PublishedBonamiBound)
    (P S : Finset ℕ) (hS : ∀ s ∈ S, Squarefree s)
    (hP : ∀ s ∈ S, s.primeFactors ⊆ P) (U M l : ℕ)
    (hU : ∀ s ∈ S, s ≤ U) (hl : 0 < l) (a : S → ℝ) :
    (∑ m ∈ Finset.range M, if Odd m then
        |∑ s : S, a s * realJacobi s.val m| ^ (2 * l) else 0) ≤
      (M : ℝ) *
        (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * |a s| ^ 2) ^ l +
      (8 * (U : ℝ) ^ (2 * l)) * (∑ s : S, |a s|) ^ (2 * l) := by
  classical
  let μ : ℕ → ℝ := fun m => if Odd m then 1 else 0
  have hμ : ∀ m ∈ Finset.range M, 0 ≤ μ m := by
    intro m hm
    dsimp [μ]
    split <;> norm_num
  have hE : 0 ≤ 8 * (U : ℝ) ^ (2 * l) := by positivity
  have hns (t : Fin (2 * l) → S) (ht : ¬IsSquare (∏ j, (t j).val)) :
      |∑ m ∈ Finset.range M, μ m * realJacobi (∏ j, (t j).val) m| ≤
        8 * (U : ℝ) ^ (2 * l) := by
    have hn : 0 < ∏ j, (t j).val := Finset.prod_pos (fun j _ =>
      Nat.pos_of_ne_zero (hS _ (t j).property).ne_zero)
    have hnU : ∏ j, (t j).val ≤ U ^ (2 * l) := by
      calc
        _ ≤ ∏ _j : Fin (2 * l), U := Finset.prod_le_prod (fun j _ => hU _ (t j).property)
        _ = _ := by simp
    have hh := nonsquare_jacobi_sum_range_bound (∏ j, (t j).val) M hn ht
    have heq : (∑ m ∈ Finset.range M, μ m * realJacobi (∏ j, (t j).val) m) =
        ∑ m ∈ Finset.range M, if Odd m then realJacobi (∏ j, (t j).val) m else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      dsimp [μ]
      split <;> simp_all
    rw [heq]
    exact hh.trans (by exact_mod_cast Nat.mul_le_mul_left 8 hnU)
  have h := weighted_jacobi_even_moment_bound hB P S (Finset.range M) hS hP μ hμ a l hl
    (8 * (U : ℝ) ^ (2 * l)) hE hns
  have hmass : (∑ m ∈ Finset.range M, μ m) ≤ M := by
    calc
      _ ≤ ∑ _m ∈ Finset.range M, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        dsimp [μ]
        split <;> norm_num
      _ = M := by simp
  have hleft : (∑ m ∈ Finset.range M, μ m * |∑ s : S, a s * realJacobi s.val m| ^ (2 * l)) =
      ∑ m ∈ Finset.range M, if Odd m then |∑ s : S, a s * realJacobi s.val m| ^ (2 * l) else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [μ]
    split <;> simp_all
  rw [hleft] at h
  exact h.trans (add_le_add_left (mul_le_mul_of_nonneg_right hmass (by positivity)) _)

end Ostmann

end OAI
