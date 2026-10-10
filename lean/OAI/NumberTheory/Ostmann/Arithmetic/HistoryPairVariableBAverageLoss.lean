import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBAverageDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryPairVariableBAverage
open Construction HistoryPairPattern HistoryPairRows HistoryPairRepresentatives
open HistoryPairSquareProbability HistoryPairKernelReplacement
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

theorem unit_square_lossAt (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (r : Representative h k)
    (hrow : ∀i : Fiber h k r,(actualLeftAt h k hs ks v r i:ZMod (prime h k r))≠0 ∨
      (actualRightAt h k hs ks v r i:ZMod (prime h k r))≠0) :
    0 ≤ actualProbability false h k hs ks r (prime h k r) v-
      actualUnitSquareProbabilityAt h k hs ks v r ∧
    actualProbability false h k hs ks r (prime h k r) v-
      actualUnitSquareProbabilityAt h k hs ks v r ≤
      ((Fintype.card (Fiber h k r):ℝ)/prime h k r)*actualProbability false h k hs ks r (prime h k r) v := by
  let : Fact (prime h k r).Prime := ⟨representative_prime h k hs ks r⟩
  have hh := unit_square_loss (prime h k r) Finset.univ (actualLeftAt h k hs ks v r)
    (actualRightAt h k hs ks v r) (fun i _ => hrow i)
  simpa only [actualUnitSquareProbabilityAt,Finset.card_univ,unit_baseAt_eq_actualProbability] using hh

theorem unit_square_product_lossAt (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (hrow : ∀r : Representative h k,∀i : Fiber h k r,
      (actualLeftAt h k hs ks v r i:ZMod (prime h k r))≠0 ∨
      (actualRightAt h k hs ks v r i:ZMod (prime h k r))≠0) :
    0 ≤ (∏r : Representative h k,actualProbability false h k hs ks r (prime h k r) v)-
      (∏r : Representative h k,actualUnitSquareProbabilityAt h k hs ks v r) ∧
    (∏r : Representative h k,actualProbability false h k hs ks r (prime h k r) v)-
      (∏r : Representative h k,actualUnitSquareProbabilityAt h k hs ks v r) ≤
      (∑i : Occurrences h k,(1:ℝ)/(slot h k i).value)*
        (∏r : Representative h k,actualProbability false h k hs ks r (prime h k r) v) := by
  rw [occurrence_reciprocal_eq_fibers]
  apply product_relative_loss
  · intro r _
    let : Fact (prime h k r).Prime := ⟨representative_prime h k hs ks r⟩
    exact probability_nonneg _
  · intro r _
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro r _
    exact unit_square_lossAt h k hs ks v r (hrow r)

theorem mixed_square_lossAt (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (r : Representative h k)
    (hrow : ∀i : Fiber h k r,(actualLeftAt h k hs ks v r i:ZMod (prime h k r))≠0 ∨
      (actualRightAt h k hs ks v r i:ZMod (prime h k r))≠0) :
    0 ≤ actualProbability true h k hs ks r (prime h k r) v-
      actualMixedSquareProbabilityAt h k hs ks v r ∧
    actualProbability true h k hs ks r (prime h k r) v-
      actualMixedSquareProbabilityAt h k hs ks v r ≤
      ((Fintype.card (Fiber h k r):ℝ)/prime h k r)*actualProbability true h k hs ks r (prime h k r) v := by
  let : Fact (prime h k r).Prime := ⟨representative_prime h k hs ks r⟩
  have hh := mixed_square_loss (prime h k r) Finset.univ (actualLeftAt h k hs ks v r)
    (actualRightAt h k hs ks v r) (fun i _ => hrow i)
  simpa only [actualMixedSquareProbabilityAt,Finset.card_univ,mixed_baseAt_eq_actualProbability] using hh

theorem mixed_square_product_lossAt (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (hrow : ∀r : Representative h k,∀i : Fiber h k r,
      (actualLeftAt h k hs ks v r i:ZMod (prime h k r))≠0 ∨
      (actualRightAt h k hs ks v r i:ZMod (prime h k r))≠0) :
    0 ≤ (∏r : Representative h k,actualProbability true h k hs ks r (prime h k r) v)-
      (∏r : Representative h k,actualMixedSquareProbabilityAt h k hs ks v r) ∧
    (∏r : Representative h k,actualProbability true h k hs ks r (prime h k r) v)-
      (∏r : Representative h k,actualMixedSquareProbabilityAt h k hs ks v r) ≤
      (∑i : Occurrences h k,(1:ℝ)/(slot h k i).value)*
        (∏r : Representative h k,actualProbability true h k hs ks r (prime h k r) v) := by
  rw [occurrence_reciprocal_eq_fibers]
  apply product_relative_loss
  · intro r _
    let : Fact (prime h k r).Prime := ⟨representative_prime h k hs ks r⟩
    exact probability_nonneg _
  · intro r _
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro r _
    exact mixed_square_lossAt h k hs ks v r (hrow r)

end Ostmann.Arithmetic.HistoryPairVariableBAverage

end

end OAI
