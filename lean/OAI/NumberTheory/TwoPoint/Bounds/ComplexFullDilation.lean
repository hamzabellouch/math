import OAI.NumberTheory.TwoPoint.Bounds.ComplexCenteredBridge

namespace OAI

/-! The full-divisibility part of the complex bin is the exact dilated correlation. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma tupleComplexPartialProfile_empty_prefix {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime) (q : ℕ) (hq : 0 < q)
    (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h N : ℕ) :
    positivePrefix (tupleComplexPartialProfile P ∅ q eligible F G h) N =
      ∑ x : (j : Fin J) → P j, if eligible (∏ j, (x j).val) q then
        positivePrefix (fun m => F ((q * ∏ j, (x j).val) * m) *
          G ((q * ∏ j, (x j).val) * (m + h))) (N / (q * ∏ j, (x j).val))
      else 0 := by
  change positivePrefix (fun n => tupleComplexPartialProfile P ∅ q eligible F G h n) N = _
  simp_rw [tupleComplexPartialProfile_empty]
  rw [positivePrefix_sum_finite]
  apply sum_congr rfl
  intro x _
  rw [positivePrefix_ite_const]
  by_cases he : eligible (∏ j, (x j).val) q
  · simp only [he, ite_true]
    have hu : 0 < q * ∏ j, (x j).val :=
      Nat.mul_pos hq (prod_pos (fun j _ => (hprime j _ (x j).property).pos))
    rw [divisibility_positivePrefix _ _ _ hu]
    congr 1
    funext m
    rw [show (q * ∏ j, (x j).val) * m + h * (q * ∏ j, (x j).val) =
      (q * ∏ j, (x j).val) * (m + h) by ring]
  · simp only [he, ite_false]

lemma fullComplexBin_eq_dilated {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, 0 < q)
    (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h : ℕ) (T : ℝ) :
    fullComplexBin P Q eligible F G h T =
      ∑ q ∈ Q, ∑ d ∈ primeTupleDivisors P, if eligible d q then
        (actualPaddingCoefficient q : ℂ) *
          (positivePrefix (fun m => F ((q * d) * m) * G ((q * d) * (m + h)))
            (⌊T⌋₊ / (q * d)) / (T : ℂ))
      else 0 := by
  unfold fullComplexBin
  apply sum_congr rfl
  intro q hq
  rw [tupleComplexPartialProfile_empty_prefix P hprime q (hQ q hq), sum_div, mul_sum,
    primeTupleDivisors, sum_image]
  · apply sum_congr rfl
    intro x _
    split_ifs <;> simp only [zero_div, mul_zero]
  · intro x _ y _ hxy
    exact primeTuple_injective hprime hdisjoint hxy

end TwoPointCorrelations

end OAI
