import OAI.NumberTheory.TwoPoint.Walks.CanonicalCorrelationDeletion
import OAI.NumberTheory.TwoPoint.Bounds.CenteredTupleProfiles

namespace OAI

/-! Identify the uncut graph sum with the literal centered-divisor
correlation, including the original (possibly nonunit) progression class. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma uncutNumericalEdge_progression (R : Finset ℕ) (eligible : ℕ → ℕ → Prop)
    (h l b d q n : ℕ) [NeZero l] (hh : 0 < h) (hd : 0 < d) (hq : 0 < q)
    (hqR : q ∈ R) :
    uncutNumericalEdge R eligible h (progressionEdgeGate h l b) d q n
      ((n : ℤ) + (h * q * d : ℕ)) =
      if eligible d q then
        (actualPaddingCoefficient q : ℂ) * natDivisibilityIndicator q n *
          (centeredTuple d.primeFactors (n : ℤ) : ℂ) *
          (progressionSequence liouville l ((b : ZMod l) * ((q * d : ℕ) : ZMod l)) n *
            liouville (n + h * (q * d)))
      else 0 := by
  have hg : progressionEdgeGate h l b d (n : ℤ) ((n : ℤ) + (h * q * d : ℕ)) ↔
      (n : ZMod l) = (b : ZMod l) * ((q * d : ℕ) : ZMod l) := by
    rw [progressionEdgeGate_on_edge h l b d q hh hd hq]
    rw [← ZMod.intCast_eq_intCast_iff]
    simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul, mul_assoc]
  have hm : (n : ℤ) + (h * q * d : ℕ) = ((n + h * (q * d) : ℕ) : ℤ) := by
    push_cast
    ring
  simp only [uncutNumericalEdge, hqR, and_true, hm, integerLiouville_natCast,
    Int.natCast_dvd_natCast, Complex.ofReal_mul]
  unfold natDivisibilityIndicator progressionSequence
  split_ifs <;> simp_all
  ring

lemma uncutPrimePrefix_centered {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (R : Finset ℕ) (hR : ∀ q ∈ R, 0 < q) (eligible : ℕ → ℕ → Prop)
    (h l b N : ℕ) [NeZero l] (hh : 0 < h) :
    uncutPrimePrefix P R eligible h (progressionEdgeGate h l b) N =
      positivePrefix (fun n => ∑ q ∈ R, (actualPaddingCoefficient q : ℂ) *
        tupleCenteredProfile P q eligible l (b : ZMod l) h n) N / (N : ℂ) := by
  unfold uncutPrimePrefix
  congr 2
  funext n
  rw [primeTupleDivisors, sum_image]
  · rw [sum_comm]
    apply sum_congr rfl
    intro q hq
    simp only [tupleCenteredProfile, mul_sum]
    apply sum_congr rfl
    intro x _
    have hd : 0 < ∏ j, (x j).val := prod_pos (fun j _ => (hprime j _ (x j).property).pos)
    rw [uncutNumericalEdge_progression R eligible h l b _ q n hh hd (hR q hq) hq]
    by_cases he : eligible (∏ j, (x j).val) q
    · simp only [he, ite_true]
      ring
    · simp only [he, ite_false, mul_zero]
  · intro x _ y _ hxy
    exact primeTuple_injective hprime hdisjoint hxy

end TwoPointCorrelations

end OAI
