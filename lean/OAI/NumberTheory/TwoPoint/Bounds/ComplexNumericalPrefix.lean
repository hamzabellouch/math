import OAI.NumberTheory.TwoPoint.Bounds.ComplexNumericalEdges
import OAI.NumberTheory.TwoPoint.Bounds.PrefixDeletionBridge
import OAI.NumberTheory.TwoPoint.Walks.RetainedEligibility

namespace OAI

/-! Numerical divisor reindexing of the arbitrary complex retained prefix. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def untwistedRetainedPrefix {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ) (N : ℕ) : ℂ :=
  positivePrefix (fun n => ∑ d ∈ primeTupleDivisors P, ∑ q ∈ Q,
    liouvilleUntwist F G n ((n : ℤ) + (h * q * d : ℕ)) *
      retainedNumericalEdge P Q Qp u eligible L K W extra h gate keep d q n
        ((n : ℤ) + (h * q * d : ℕ))) N / (N : ℂ)

noncomputable def untwistedUncutPrefix {J : ℕ} (P : Fin J → Finset ℕ)
    (Q : Finset ℕ) (eligible : ℕ → ℕ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (F G : ℤ → ℂ) (N : ℕ) : ℂ :=
  positivePrefix (fun n => ∑ d ∈ primeTupleDivisors P, ∑ q ∈ Q,
    liouvilleUntwist F G n ((n : ℤ) + (h * q * d : ℕ)) *
      uncutNumericalEdge Q eligible h gate d q n ((n : ℤ) + (h * q * d : ℕ))) N / (N : ℂ)

lemma retainedComplex_row_eq_numerical {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i k, k ≠ i → Disjoint (P i) (P k))
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ)
    (n : ℤ) (hn : 0 < n) (hL : L ≠ 0) :
    (∑ e : ((j : Fin J) → P j) × Q,
      retainedComplexPrimeEdge P Q Qp u eligible L K W extra h gate keep F G e n
        (n + (h * e.2.val * ∏ j, (e.1 j).val : ℕ))) / (L : ℂ) =
      ∑ d ∈ primeTupleDivisors P, ∑ q ∈ Q,
        liouvilleUntwist F G n (n + (h * q * d : ℕ)) *
          retainedNumericalEdge P Q Qp u eligible L K W extra h gate keep d q n
            (n + (h * q * d : ℕ)) := by
  rw [sum_div, Fintype.sum_prod_type, primeTupleDivisors, sum_image]
  · apply sum_congr rfl
    intro d _
    calc
      _ = ∑ q : Q, liouvilleUntwist F G n (n + (h * q.val * ∏ j, (d j).val : ℕ)) *
          retainedNumericalEdge P Q Qp u eligible L K W extra h gate keep
            (∏ j, (d j).val) q.val n (n + (h * q.val * ∏ j, (d j).val : ℕ)) := by
        apply sum_congr rfl
        intro q _
        exact retainedComplexPrimeEdge_eq_untwist P Q Qp u eligible L K W extra h gate keep
          F G (d, q) n _ hn (by omega) hL
      _ = _ := sum_coe_sort Q (fun q =>
        liouvilleUntwist F G n (n + (h * q * ∏ j, (d j).val : ℕ)) *
          retainedNumericalEdge P Q Qp u eligible L K W extra h gate keep
            (∏ j, (d j).val) q n (n + (h * q * ∏ j, (d j).val : ℕ)))
  · intro d _ e _ hde
    exact primeTuple_injective hprime hdisjoint hde

lemma retainedComplexPrefix_eq_numerical {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i k, k ≠ i → Disjoint (P i) (P k))
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ) (N : ℕ)
    (hL : L ≠ 0) :
    retainedComplexPrefix P Q Qp u eligible L K W extra h gate keep F G N =
      untwistedRetainedPrefix P Q Qp u eligible L K W extra h gate keep F G N := by
  unfold retainedComplexPrefix untwistedRetainedPrefix
  rw [div_right_comm]
  congr 1
  unfold positivePrefix
  rw [sum_div]
  apply sum_congr rfl
  intro n _
  exact retainedComplex_row_eq_numerical P hprime hdisjoint Q Qp u eligible L K W extra h
    gate keep F G (n + 1 : ℕ) (by omega) hL

lemma untwistedRetainedPrefix_congr_eligible {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (u : ℕ → ℝ) (e f : ℕ → ℕ → Prop) (L K W : ℝ)
    (extra : ℕ → ℤ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (keep : ℤ → Prop) (F G : ℤ → ℂ) (N : ℕ)
    (hef : ∀ d ∈ primeTupleDivisors P, ∀ q ∈ R, e d q ↔ f d q) :
    untwistedRetainedPrefix P R Q u e L K W extra h gate keep F G N =
      untwistedRetainedPrefix P R Q u f L K W extra h gate keep F G N := by
  unfold untwistedRetainedPrefix
  congr 2
  funext n
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro q hq
  rw [retainedNumericalEdge_congr_eligible P R Q u e f L K W extra h gate keep
    d q n ((n : ℤ) + (h * q * d : ℕ)) hq (hef d hd)]

end TwoPointCorrelations

end OAI
