import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSignedInfiniteSum

namespace OAI

/-! # The exact finite cutoff in the odd-squarefree frequency variable -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadraticOddKernel_val_injective :
    Function.Injective (fun b : QuadraticOddKernel => (b.val : ℕ)) := by
  intro b c h
  exact Subtype.ext (Subtype.ext h)

theorem quadratic_odd_kernel_cutoff (K : ℕ) (F : ℕ → ℂ) :
    (∑' b : QuadraticOddKernel, if (b.val : ℕ) ≤ K then F b.val else 0) =
      ∑ b ∈ oddSquarefreeRange K, F b := by
  let G : ℕ → ℂ := fun n => if n ∈ oddSquarefreeRange K then F n else 0
  have he : (∑' b : QuadraticOddKernel, G b.val) = ∑' n : ℕ, G n := by
    apply quadraticOddKernel_val_injective.tsum_eq
    intro n hn
    have hnS : n ∈ oddSquarefreeRange K := by
      by_contra hs
      exact hn (by simp only [G, hs, ite_false])
    obtain ⟨hr, ho, hsf⟩ := Finset.mem_filter.mp hnS
    exact ⟨⟨⟨n, (Finset.mem_Icc.mp hr).1⟩, ho, hsf⟩, rfl⟩
  calc
    _ = ∑' b : QuadraticOddKernel, G b.val := by
      apply tsum_congr
      intro b
      have hm : (b.val : ℕ) ∈ oddSquarefreeRange K ↔ (b.val : ℕ) ≤ K := by
        simp only [oddSquarefreeRange, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨fun h => h.1.2, fun h => ⟨⟨b.val.property, h⟩, b.property⟩⟩
      simp only [G, hm]
    _ = ∑' n : ℕ, G n := he
    _ = _ := by
      rw [tsum_eq_sum (s := oddSquarefreeRange K) (by
        intro n hn
        simp only [G, hn, ite_false])]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [G, hn, ite_true]

theorem quadratic_odd_kernel_split (K : ℕ) (F : ℕ → ℂ)
    (hF : Summable (fun b : QuadraticOddKernel => F b.val)) :
    (∑' b : QuadraticOddKernel, F b.val) =
      (∑ b ∈ oddSquarefreeRange K, F b) +
        ∑' b : QuadraticOddKernel, if K < (b.val : ℕ) then F b.val else 0 := by
  have hlow : Summable (fun b : QuadraticOddKernel =>
      if (b.val : ℕ) ≤ K then F b.val else 0) := by
    apply Summable.of_norm_bounded hF.norm
    intro b
    split_ifs <;> simp
  have hhigh : Summable (fun b : QuadraticOddKernel =>
      if K < (b.val : ℕ) then F b.val else 0) := by
    apply Summable.of_norm_bounded hF.norm
    intro b
    split_ifs <;> simp
  rw [← quadratic_odd_kernel_cutoff K F, ← hlow.tsum_add hhigh]
  apply tsum_congr
  intro b
  by_cases hb : (b.val : ℕ) ≤ K
  · simp only [hb, not_lt.mpr hb, ite_true, ite_false, add_zero]
  · simp only [hb, lt_of_not_ge hb, ite_true, ite_false, zero_add]

end Ostmann

end OAI
