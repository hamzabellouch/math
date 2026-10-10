import OAI.NumberTheory.Ostmann.Preliminaries.MultiplicativeSieveProof

namespace OAI

/-! # Packing an arbitrary finite support into its actual integer interval -/

namespace Ostmann

open scoped BigOperators Classical

 theorem finite_interval_sum {A : Type*} [AddCommMonoid A]
    (S : Finset ℕ) (J M : ℕ) (hS : ∀ n ∈ S, J ≤ n ∧ n < J + M) (f : ℕ → A) :
    (∑ n ∈ S, f n) = ∑ j : Fin M, if J + j.val ∈ S then f (J + j.val) else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun n hn =>
    (⟨n - J, by have hh := hS n hn; omega⟩ : Fin M))
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hnJ := (hS n hn).1
    simpa only [Nat.add_sub_of_le hnJ] using hn
  · intro n hn m hm he
    have hval := congrArg Fin.val he
    have hnJ := (hS n hn).1
    have hmJ := (hS m hm).1
    dsimp at hval
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨J + j.val, hj, ?_⟩
    apply Fin.ext
    simp
  · intro n hn
    have hnJ := (hS n hn).1
    simp only [Nat.add_sub_of_le hnJ]

 theorem finite_support_multiplicative_sieve (S : Finset ℕ) (J M Q : ℕ)
    (hM : 1 ≤ M) (hQ : 1 ≤ Q) (hS : ∀ n ∈ S, J ≤ n ∧ n < J + M)
    (c : ℕ → ℂ) (F : (q : ℕ) → Finset (DirichletCharacter ℂ q))
    (hF : ∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
      ‖∑ n ∈ S, c n * χ (n : ZMod q)‖ ^ 2) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ S, ‖c n‖ ^ 2 := by
  let b : Fin M → ℂ := fun j => if J + j.val ∈ S then c (J + j.val) else 0
  have hs (q : ℕ) (χ : DirichletCharacter ℂ q) :
      (∑ n ∈ S, c n * χ (n : ZMod q)) =
        ∑ j : Fin M, b j * χ (((J : ℤ) + (j.val : ℤ) : ℤ) : ZMod q) := by
    rw [finite_interval_sum S J M hS]
    apply Finset.sum_congr rfl
    intro j _
    simp only [b, Int.cast_add, Int.cast_natCast]
    split_ifs <;> simp [Nat.cast_add]
  have he : (∑ n ∈ S, ‖c n‖ ^ 2) = ∑ j : Fin M, ‖b j‖ ^ 2 := by
    rw [finite_interval_sum S J M hS]
    apply Finset.sum_congr rfl
    intro j _
    simp only [b]
    split_ifs <;> simp
  simp_rw [hs]
  rw [he]
  exact primitive_multiplicative_large_sieve M Q hM hQ J b F hF

end Ostmann

end OAI
