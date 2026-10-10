import OAI.NumberTheory.TwoPoint.Bounds.ActualRetainedPrefix
import OAI.NumberTheory.TwoPoint.Bounds.ProgressionGateOnEdge

namespace OAI

/-! Reindex the retained prefix by the original numerical divisors,
with no tuple-representation multiplicity. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def retainedNumericalEdge {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (d q : ℕ) (n m : ℤ) : ℂ :=
  if gate d n m ∧ keep n ∧ keep m then
    retainedLiouvilleEdge Q u (eligible d) (actualPaddingVertex Qp)
      (centeredTuple d.primeFactors) L K (extra d)
      (fun z => (actualPaddingDegree (univ.biUnion P) z : ℝ) ≤ 6 * W * J ∧
        actualPaddingDegreeCut Qp L z) h d q n m
  else 0

lemma retainedPrimeEdge_eq_numerical {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    (e : ((j : Fin J) → P j) × Q) (n m : ℤ) :
    retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n m =
      retainedNumericalEdge P Q Qp u eligible L K W extra h gate keep
        (∏ j, (e.1 j).val) e.2.val n m := rfl

lemma retained_tuple_sum_eq_numerical {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (n : ℤ) :
    (∑ e : ((j : Fin J) → P j) × Q,
      retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n
        (n + (h * e.2.val * ∏ j, (e.1 j).val : ℕ))) =
      ∑ d ∈ primeTupleDivisors P, ∑ q ∈ Q,
        retainedNumericalEdge P Q Qp u eligible L K W extra h gate keep d q n
          (n + (h * q * d : ℕ)) := by
  rw [Fintype.sum_prod_type, primeTupleDivisors, sum_image]
  · apply sum_congr rfl
    intro d _
    simp only [retainedPrimeEdge_eq_numerical]
    exact sum_coe_sort Q (fun q => retainedNumericalEdge P Q Qp u eligible
      L K W extra h gate keep (∏ j, (d j).val) q n
      (n + (h * q * ∏ j, (d j).val : ℕ)))
  · intro d _ e _ hde
    exact primeTuple_injective hprime hdisjoint hde

theorem retainedPrimePrefix_eq_numerical {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (N : ℕ) :
    retainedPrimePrefix P Q Qp u eligible L K W extra h gate keep N =
      positivePrefix (fun n => ∑ d ∈ primeTupleDivisors P, ∑ q ∈ Q,
        retainedNumericalEdge P Q Qp u eligible L K W extra h gate keep d q n
          ((n : ℤ) + (h * q * d : ℕ))) N / (N : ℂ) := by
  unfold retainedPrimePrefix
  simp_rw [retained_tuple_sum_eq_numerical P hprime hdisjoint]

lemma positivePrefix_real_denominator_le (F : ℕ → ℂ) (T : ℝ) (hT : 1 ≤ T) :
    ‖positivePrefix F ⌊T⌋₊ / (T : ℂ)‖ ≤
      ‖positivePrefix F ⌊T⌋₊ / (⌊T⌋₊ : ℂ)‖ := by
  have hN : 0 < ⌊T⌋₊ := (Nat.le_floor_iff (by linarith : 0 ≤ T)).mpr (by simpa using hT)
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ T),
    Complex.norm_natCast]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (Nat.floor_le (by linarith))

end TwoPointCorrelations

end OAI
