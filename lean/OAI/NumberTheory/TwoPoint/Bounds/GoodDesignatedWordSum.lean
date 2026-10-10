import OAI.NumberTheory.TwoPoint.Walks.GoodWordForest
import OAI.NumberTheory.TwoPoint.Bounds.GoodWeightedDifferenceSum
import OAI.NumberTheory.TwoPoint.Bounds.AmbientTupleLabels

namespace OAI

/-! The actual good designated-word sum: forced residues, literal deletions and retained padding weights. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma budgetColumnArray_cover_congr {n J N M : ℕ} {L : ℝ}
    (hn : n ≤ N) (hm : n ≤ M) (he : N = M)
    (pattern : Fin J → Fin n → Fin n → Bool)
    (hc : ∃ code : BudgetColumnArrayCode J N L,
      ∀ j i l, decodeBudgetColumnArray hn code j i l = pattern j i l) :
    ∃ code : BudgetColumnArrayCode J M L,
      ∀ j i l, decodeBudgetColumnArray hm code j i l = pattern j i l := by
  subst M
  exact hc

noncomputable def tupleForcedTarget {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (word : List SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (t : Fin R × Fin J) : Fin B :=
  forcedResidue B (label t).val (data.prime _).pos (hB _ (label t).property)
    (wordDisplacement h (word.take t.1.val))

noncomputable def prohibitedWordDifference {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (word : List SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B) (U : Finset (Fin R × Fin J))
    (x : ↥(data.P ∪ data.Q) → Fin B) : ℝ :=
  selectedMixedDifference (singletonLabels label)
    (singletonTarget label (tupleForcedTarget data hB word label) base)
    (fun y => attachedCatalogAvoidance data s B D word
      (forceCoordinates ((nonsingletonSlots label \ U).image label)
        (litForcedTarget (nonsingletonSlots label \ U) label
          (tupleForcedTarget data hB word label) base) y)) x

lemma prohibitedWordDifference_abs_le {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (word : List SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B) (U : Finset (Fin R × Fin J))
    (x : ↥(data.P ∪ data.Q) → Fin B) :
    |prohibitedWordDifference data hB s D word label base U x| ≤
      2 ^ (singletonLabels label).card := by
  apply selectedMixedDifference_bound
  intro y
  exact witnessAvoidance_abs_le_one _ _

theorem good_designated_word_sum {h J M B s D k S r : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (F : Finset (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)))
    (hR : 0 < 2 * k) (forward : Fin (2 * k) → Bool)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (hpairs : ∀ a ∈ F, ∀ i, (columnTuple a.1 i, (a.2 i).val) ∈ data.pairs)
    (hRD : 2 * k ≤ D)
    (label : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) →
      Fin (2 * k) × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ a ∈ F, ∀ i j, (label a (i, j)).val = (a.1 j i).val)
    (base : ↥(data.P ∪ data.Q) → Fin B) (U : Finset (Fin (2 * k) × Fin J))
    (hU : ∀ a ∈ F, U ⊆ nonsingletonSlots (label a))
    (hLit : ∀ a ∈ F, LitConsistent (nonsingletonSlots (label a) \ U) (label a)
      (tupleForcedTarget data hB (columnTupleWord a.1 forward (fun i => (a.2 i).val)) (label a)))
    (weight : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) →
      (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (hweight : ∀ a ∈ F, ∀ y z, (∀ i, i ∉ univ.image (label a) → y i = z i) →
      weight a y = weight a z)
    (hpadding : ∀ a ∈ F, ∀ x, weight a x ≠ 0 → MainPaddingTests
      (fun p : ↥(data.P ∪ data.Q) => p.val) h B
      (columnTupleWord a.1 forward (fun i => (a.2 i).val)) x)
    (hh : 0 < h) (hs : 0 < s) (cut : Fin (2 * k))
    (hleft : ∀ a ∈ F, ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).take cut.val).IsChain
      (fun a b => a.tuple ≠ b.tuple))
    (hright : ∀ a ∈ F, ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).drop cut.val).IsChain
      (fun a b => a.tuple ≠ b.tuple))
    (L K A : ℝ) (hL : 1 ≤ L) (hRL : (2 * k : ℕ) ≤ 2 * L)
    (hsL : L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ))
    (hrL : (r : ℝ) ≤ L ^ (1 / 50 : ℝ))
    (hI : ∀ a ∈ F, (imperfectColumnCount ((perfectRows (label a) U).erase cut) : ℝ) ≤
      2 * L ^ (1 / 4 : ℝ))
    (hno : ∀ a ∈ F, ∀ j, ColumnLowRank
      (tupleColumnPattern a.1 hR forward (fun i => (a.2 i).val) j)
      hR h (perfectRows (label a) U) cut r)
    (u : ℕ → ℝ) (eligible : ColumnPrimeAssignment J (2 * k) P → ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (extra : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → Prop)
    (next : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → ℕ → ℤ)
    (origin : (↥(data.P ∪ data.Q) → Fin B) → ℤ)
    (hK : 0 ≤ K) (hA : 1 ≤ A) (hu : ∀ q, 0 ≤ u q)
    (hmass : ∀ j, primeHarmonicMass (P j) ≤ A)
    (hsingle : ∀ a ∈ F, columnSingletonCount a.1 ≤ 2 * S)
    (hw : ∀ a ∈ F, ∀ x, 0 ≤ weight a x)
    (hpad : ∀ a ∈ F, ∀ x, weight a x ≤
      retainedColumnPaddingWeight Q u eligible g L K extra next (origin x) a.1 a.2) :
    (∑ a ∈ F, designatedReciprocal (fun p : ↥(data.P ∪ data.Q) => p.val)
      (singletonLabels (label a)) (nonsingletonSlots (label a) \ U) U (label a) *
      (data.residueLaw B hB).average (fun x => weight a x *
        |prohibitedWordDifference data hB s D
          (columnTupleWord a.1 forward (fun i => (a.2 i).val)) (label a) base U x|)) ≤
      (2 : ℝ) ^ (2 * S) * ((Fintype.card (BudgetColumnArrayCode J (4 * k) L) : ℝ) *
        K ^ (2 * k) * A ^ (J * k + S)) := by
  let delta a := prohibitedWordDifference data hB s D
    (columnTupleWord a.1 forward (fun i => (a.2 i).val)) (label a) base U
  apply le_trans _ (good_weighted_difference_sum (data.residueLaw B hB) P Q F
    (decodeBudgetColumnArray (show 2 * k ≤ 4 * k by omega)) u eligible g L K A
    (2 ^ (2 * S)) extra next origin weight delta (by linarith) hK hA (by positivity)
    hu hmass hsingle hw hpad ?_ ?_)
  · apply sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_right
      (designatedReciprocal_le_tuple a.1 hdisjoint _ Subtype.val_injective
        (fun p => (data.prime p).pos) (label a) (hlabel a ha) U (hU a ha))
      ((data.residueLaw B hB).average_nonneg
        (fun x => mul_nonneg (hw a ha x) (abs_nonneg _)))
  · intro a ha x
    apply (prohibitedWordDifference_abs_le data hB s D _ _ base U x).trans
    apply pow_le_pow_right₀ (by norm_num)
    rw [tuple_label_singleton_count a.1 hdisjoint _ Subtype.val_injective _ (hlabel a ha)]
    exact hsingle a ha
  · intro a ha x hx hd
    apply budgetColumnArray_cover_congr (show 2 * k ≤ 2 * (2 * k) by omega)
      (show 2 * k ≤ 4 * k by omega) (show 2 * (2 * k) = 4 * k by omega)
      (fun j i l => decide (a.1 j i = a.1 j l))
    exact good_word_column_cover data P a.1 hR forward (fun i => (a.2 i).val)
      hprime hdisjoint (hpairs a ha) hB hRD (label a) (hlabel a ha) U base x
      (weight a) (hweight a ha) (hpadding a ha) hx (hLit a ha) hd hh hs cut
      (hleft a ha) (hright a ha) L hL hRL hsL hrL (hI a ha) (hno a ha)

end TwoPointCorrelations

end OAI
