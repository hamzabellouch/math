import OAI.NumberTheory.Ostmann.HybridSieve.ShiftedSieve

namespace OAI

open scoped Classical
namespace Ostmann.HybridSieve

lemma sum_support_interval {E : Type*} [AddCommMonoid E]
    (s : Finset ℕ) (f : ℕ → E) (A M : ℕ)
    (hf : ∀ n ∈ s, f n ≠ 0 → A ≤ n ∧ n < A+M) :
    ∑ n ∈ s, f n = ∑ j : Fin M, if A+j.val ∈ s then f (A+j.val) else 0 := by
  calc
    _ = ∑ n ∈ Finset.Ico A (A+M), if n ∈ s then f n else 0 := by
      apply Finset.sum_congr_of_eq_on_inter
      · intro n hn hnot
        by_contra hne
        exact hnot (Finset.mem_Ico.mpr (hf n hn hne))
      · intro n _ hn
        simp [hn]
      · intro n hn _
        simp [hn]
    _ = _ := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left, Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      simp [Finset.mem_range.mp hj]

theorem interval_multiplicative_large_sieve (s : Finset ℕ) (a : ℕ → ℂ)
    (A M Q : ℕ) (ha : ∀ n ∈ s, a n ≠ 0 → A ≤ n ∧ n < A+M) :
    (∑ q : Fin Q, ((q.val+1:ℕ):ℝ)/((q.val+1).totient:ℝ) *
      (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q.val+1))).filter
        (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ s, a n * χ (n : ZMod (q.val+1))‖^2)) ≤
      ((M:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ)) * ∑ n ∈ s, ‖a n‖^2 := by
  let b : Fin M → ℂ := fun j => if A+j.val ∈ s then a (A+j.val) else 0
  have hchar (q : ℕ) (χ : DirichletCharacter ℂ q) :
      (∑ n ∈ s, a n * χ (n : ZMod q)) = shiftedCharacterSum A b χ := by
    rw [sum_support_interval s (fun n => a n * χ (n : ZMod q)) A M]
    · unfold shiftedCharacterSum
      apply Finset.sum_congr rfl
      intro j _
      dsimp [b]
      split_ifs <;> simp
    · intro n hn hne
      exact ha n hn (left_ne_zero_of_mul hne)
  have hnorm : (∑ n ∈ s, ‖a n‖^2) = ∑ j : Fin M, ‖b j‖^2 := by
    rw [sum_support_interval s (fun n => ‖a n‖^2) A M]
    · apply Finset.sum_congr rfl
      intro j _
      dsimp [b]
      split_ifs <;> simp
    · intro n hn hne
      apply ha n hn
      intro hzero
      simp [hzero] at hne
  simp_rw [hchar, hnorm]
  exact shifted_multiplicative_large_sieve A Q M b

end Ostmann.HybridSieve

end OAI
