import OAI.NumberTheory.TwoPoint.Bounds.NonrawReindex
import OAI.NumberTheory.TwoPoint.Bounds.DivisibilityPrefix

namespace OAI

/-! Exact finite-prefix assembly of the nonraw expansion at the retained
divisor scale. No endpoint terms are discarded. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma positivePrefix_finset_sum (U : Finset ℕ) (F : ℕ → ℕ → ℂ) (X : ℕ) :
    positivePrefix (fun n => ∑ u ∈ U, F u n) X =
      ∑ u ∈ U, positivePrefix (F u) X := by
  unfold positivePrefix
  exact sum_comm

lemma positivePrefix_const_mul (c : ℂ) (F : ℕ → ℂ) (X : ℕ) :
    positivePrefix (fun n => c * F n) X = c * positivePrefix F X := by
  simp only [positivePrefix, mul_sum]

theorem centerDifference_prefix (S T C : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (hT : T ⊆ S) (hCT : Disjoint C T)
    (a : ℕ → ℂ) (A H τ : ℝ) (θ : ℂ) (F : ℕ → ℕ → ℂ) (X : ℕ) :
    positivePrefix (fun x => centerDifference S T C a A H τ θ x (F x)) X =
      ∑ u ∈ retainedPrimeDivisors S, (A : ℂ) ^ (u.primeFactors ∩ C).card *
        ∑ w ∈ nonrawRoughSupport T H τ u,
          ((nonrawRoughData T H τ a θ u).coefficient w / (w : ℂ)) *
            positivePrefix (fun z => F (u * z) (u * w)) (X / u) := by
  have hpoint (x : ℕ) : centerDifference S T C a A H τ θ x (F x) =
      ∑ u ∈ retainedPrimeDivisors S, (A : ℂ) ^ (u.primeFactors ∩ C).card *
        ∑ w ∈ nonrawRoughSupport T H τ u,
          ((nonrawRoughData T H τ a θ u).coefficient w / (w : ℂ)) *
            (natDivisibilityIndicator u x * F x (u * w)) := by
    rw [centerDifference_eq_nonraw_sum S T C hS hT hCT a A H τ θ x (F x)]
    apply sum_congr rfl
    intro u _
    congr 1
    apply sum_congr rfl
    intro w _
    ring
  calc
    _ = positivePrefix (fun x =>
        ∑ u ∈ retainedPrimeDivisors S, (A : ℂ) ^ (u.primeFactors ∩ C).card *
          ∑ w ∈ nonrawRoughSupport T H τ u,
            ((nonrawRoughData T H τ a θ u).coefficient w / (w : ℂ)) *
              (natDivisibilityIndicator u x * F x (u * w))) X := by
      congr 1
      funext x
      exact hpoint x
    _ = ∑ u ∈ retainedPrimeDivisors S, (A : ℂ) ^ (u.primeFactors ∩ C).card *
        ∑ w ∈ nonrawRoughSupport T H τ u,
          ((nonrawRoughData T H τ a θ u).coefficient w / (w : ℂ)) *
            positivePrefix (fun x => natDivisibilityIndicator u x * F x (u * w)) X := by
      rw [positivePrefix_finset_sum]
      apply sum_congr rfl
      intro u _
      rw [positivePrefix_const_mul, positivePrefix_finset_sum]
      congr 1
      apply sum_congr rfl
      intro w _
      exact positivePrefix_const_mul _ _ _
    _ = _ := by
      apply sum_congr rfl
      intro u hu
      congr 1
      apply sum_congr rfl
      intro w _
      rw [divisibility_positivePrefix _ u X (retainedPrimeDivisor_pos S hS hu)]

end TwoPointCorrelations

end OAI
