import OAI.NumberTheory.Ostmann.Arithmetic.MovingLeafAmplitude
import OAI.NumberTheory.Ostmann.Construction.ScheduledHistoryEmbedding

namespace OAI

/-! # The two original scheduled histories as one paired frequency tree -/

namespace Ostmann
open scoped Classical BigOperators

def pairFrequencyTrees (S : Finset ℤ) : (n : ℕ) →
    FrequencyTree S n → FrequencyTree S n → FrequencyTree (S × S) n
  | 0, a, b => (a, b)
  | n + 1, a, b => ((a.1, b.1), pairFrequencyTrees S n a.2.1 b.2.1,
      pairFrequencyTrees S n a.2.2 b.2.2)

theorem frequencyPairProjection_pair (S : Finset ℤ) (n : ℕ)
    (a b : FrequencyTree S n) (side : Bool) :
    frequencyPairProjection S n side (pairFrequencyTrees S n a b) = if side then b else a := by
  induction n with
  | zero => cases side <;> rfl
  | succ n ih =>
    change ((if side then b.1 else a.1),
      frequencyPairProjection S n side (pairFrequencyTrees S n a.2.1 b.2.1),
      frequencyPairProjection S n side (pairFrequencyTrees S n a.2.2 b.2.2)) = _
    rw [ih, ih]
    cases side <;> rfl

theorem pairFrequencyTrees_projections (S : Finset ℤ) (n : ℕ)
    (t : FrequencyTree (S × S) n) :
    pairFrequencyTrees S n (frequencyPairProjection S n false t)
      (frequencyPairProjection S n true t) = t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (t.1,
      pairFrequencyTrees S n (frequencyPairProjection S n false t.2.1)
        (frequencyPairProjection S n true t.2.1),
      pairFrequencyTrees S n (frequencyPairProjection S n false t.2.2)
        (frequencyPairProjection S n true t.2.2)) = t
    rw [ih, ih]
    rcases t with ⟨a, b, c⟩
    rfl

/-- No multiplicity is lost when the two independent descendant histories
are placed in the paired tree used by the arithmetic norm estimate. -/
def pairedFrequencyEquiv (S : Finset ℤ) (n : ℕ) :
    (FrequencyTree S n × FrequencyTree S n) ≃ FrequencyTree (S × S) n where
  toFun t := pairFrequencyTrees S n t.1 t.2
  invFun t := (frequencyPairProjection S n false t, frequencyPairProjection S n true t)
  left_inv t := by simp only [frequencyPairProjection_pair, Bool.false_eq_true, ite_false, ite_true]
  right_inv := pairFrequencyTrees_projections S n

noncomputable def pairedScheduledHistoryEmbedding (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ) :
    (NonzeroScheduledHistory V n × NonzeroScheduledHistory V n) ↪
      FrequencyTree (((transferFrequencyRange (V n)).erase 0) ×
        ((transferFrequencyRange (V n)).erase 0)) n :=
  (Function.Embedding.prodMap (scheduledHistoryEmbedding V hV n) (scheduledHistoryEmbedding V hV n)).trans
    (pairedFrequencyEquiv ((transferFrequencyRange (V n)).erase 0) n).toEmbedding

theorem pairedScheduledHistoryEmbedding_projection (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (a : NonzeroScheduledHistory V n × NonzeroScheduledHistory V n) (side : Bool) :
    frequencyTreeMap Subtype.val n
      (frequencyPairProjection ((transferFrequencyRange (V n)).erase 0) n side
        (pairedScheduledHistoryEmbedding V hV n a)) =
      scheduledFrequencyHistory V n (if side then a.2.val else a.1.val) := by
  change frequencyTreeMap Subtype.val n (frequencyPairProjection _ n side
    (pairFrequencyTrees _ n (scheduledHistoryEmbedding V hV n a.1)
      (scheduledHistoryEmbedding V hV n a.2))) = _
  rw [frequencyPairProjection_pair]
  cases side <;> exact scheduledHistoryEmbedding_map V hV n _

/-- Passing to a common internal cutoff retains the actual bottom cutoff on
both sides of the original square. -/
theorem pairedScheduledHistoryEmbedding_leaf (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (a : NonzeroScheduledHistory V n × NonzeroScheduledHistory V n) :
    frequencyLeafWeight (pairedFrequencyLeaf ((transferFrequencyRange (V n)).erase 0) (V 0)) n
      (pairedScheduledHistoryEmbedding V hV n a) = 1 := by
  rw [← frequencyLeafWeight_pair_projection]
  change frequencyLeafWeight _ n
      (frequencyPairProjection _ n false (pairFrequencyTrees _ n (scheduledHistoryEmbedding V hV n a.1)
        (scheduledHistoryEmbedding V hV n a.2))) *
    frequencyLeafWeight _ n
      (frequencyPairProjection _ n true (pairFrequencyTrees _ n (scheduledHistoryEmbedding V hV n a.1)
        (scheduledHistoryEmbedding V hV n a.2))) = 1
  simp only [frequencyPairProjection_pair, Bool.false_eq_true, ite_false, ite_true,
    scheduledHistoryEmbedding_leaf_cutoff, one_mul]

end Ostmann

end OAI
