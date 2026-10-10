import OAI.NumberTheory.TwoPoint.Walks.GoodWordHybrid
import OAI.NumberTheory.TwoPoint.Walks.TupleColumnCover
import OAI.NumberTheory.TwoPoint.Walks.TuplePrimeArithmetic

namespace OAI

/-! The surviving actual mixed difference supplies the forest cover, including its arithmetic hypotheses. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma ProhibitedPrimeFamily.supplied_word_support {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (word : List SignedStep)
    (hpairs : ∀ a ∈ word, (a.tuple, a.padding) ∈ data.pairs)
    (p v : ℕ) (hp : TuplePrimeAt word p v) :
    ¬p ∣ h ∧ ∀ a ∈ word, ¬p ∣ a.padding := by
  obtain ⟨hpprime, t, ht, hpt⟩ := hp
  have htword := List.mem_of_getElem? ht
  have htpair := hpairs t htword
  have hpP : p ∈ data.P := data.tuple_pool _ htpair
    (hpprime.mem_primeFactors hpt (data.tuple_squarefree _ htpair).ne_zero)
  refine ⟨data.excluded p hpP, ?_⟩
  intro a ha hpa
  have hapair := hpairs a ha
  have hpQ : p ∈ data.Q := data.padding_pool _ hapair
    (hpprime.mem_primeFactors hpa (data.padding_squarefree _ hapair).ne_zero)
  exact disjoint_left.mp data.disjoint hpP hpQ

theorem good_word_column_cover {h J M B s D R r : ℕ}
    (data : ProhibitedPrimeFamily h J M) (P : Fin J → Finset ℕ)
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (hpairs : ∀ i, (columnTuple w i, padding i) ∈ data.pairs)
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (hRD : R ≤ D)
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val)
    (U : Finset (Fin R × Fin J)) (base x : ↥(data.P ∪ data.Q) → Fin B)
    (weight : (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (hweight : ∀ y z, (∀ i, i ∉ univ.image label → y i = z i) → weight y = weight z)
    (hpadding : ∀ y, weight y ≠ 0 → MainPaddingTests
      (fun p : ↥(data.P ∪ data.Q) => p.val) h B (columnTupleWord w forward padding) y)
    (hx : weight x ≠ 0)
    (hL : LitConsistent (nonsingletonSlots label \ U) label
      (fun t => forcedResidue B (label t).val (data.prime _).pos (hB _ (label t).property)
        (wordDisplacement h ((columnTupleWord w forward padding).take t.1.val))))
    (hnz : selectedMixedDifference (singletonLabels label)
      (singletonTarget label
        (fun t => forcedResidue B (label t).val (data.prime _).pos (hB _ (label t).property)
          (wordDisplacement h ((columnTupleWord w forward padding).take t.1.val))) base)
      (fun z => attachedCatalogAvoidance data s B D (columnTupleWord w forward padding)
        (forceCoordinates ((nonsingletonSlots label \ U).image label)
          (litForcedTarget (nonsingletonSlots label \ U) label
            (fun t => forcedResidue B (label t).val (data.prime _).pos (hB _ (label t).property)
              (wordDisplacement h ((columnTupleWord w forward padding).take t.1.val))) base) z)) x ≠ 0)
    (hh : 0 < h) (hs : 0 < s) (cut : Fin R)
    (hleft : ((columnTupleWord w forward padding).take cut.val).IsChain
      (fun a b => a.tuple ≠ b.tuple))
    (hright : ((columnTupleWord w forward padding).drop cut.val).IsChain
      (fun a b => a.tuple ≠ b.tuple))
    (L : ℝ) (hLone : 1 ≤ L) (hRL : (R : ℝ) ≤ 2 * L)
    (hsL : L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ))
    (hrL : (r : ℝ) ≤ L ^ (1 / 50 : ℝ))
    (hI : (imperfectColumnCount ((perfectRows label U).erase cut) : ℝ) ≤
      2 * L ^ (1 / 4 : ℝ))
    (hno : ∀ j, ColumnLowRank (tupleColumnPattern w hR forward padding j)
      hR h (perfectRows label U) cut r) :
    ∃ code : BudgetColumnArrayCode J (2 * R) L,
      ∀ j i l, decodeBudgetColumnArray (show R ≤ 2 * R by omega) code j i l =
        decide (w j i = w j l) := by
  let step : Fin R → SignedStep := fun i => ⟨forward i, columnTuple w i, padding i⟩
  have hlabels : ∀ i (p : ↥(data.P ∪ data.Q)), p.val ∈ (step i).tuple.primeFactors →
      ∃ j, label (i, j) = p := by
    intro i p hp
    change p.val ∈ (columnTuple w i).primeFactors at hp
    rw [columnTuple_primeFactors w i hprime hdisjoint] at hp
    obtain ⟨j, _, hj⟩ := mem_image.mp hp
    exact ⟨j, Subtype.ext ((hlabel i j).trans hj)⟩
  obtain ⟨n, hn, havoid⟩ := good_word_integer_hybrid data step hpairs hB hRD label
    hlabels U base x weight hweight hpadding hx hL hnz
  have hpairword : ∀ a ∈ columnTupleWord w forward padding,
      (a.tuple, a.padding) ∈ data.pairs := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hpairs i
  apply tuple_column_array_cover P w hR forward padding hprime hdisjoint
    (supply := fun d q => (d, q) ∈ data.pairs) (x := n) hh hs
    (perfectRows label U) cut ?_ hpairword ?_ ?_ ?_ hleft hright
    (data.supplied_word_support _ hpairword) ?_ L hLone hRL hsL hrL hI hno
  · intro i hi
    simpa only [step, SignedStep.divisor, columnTupleWord] using hn i hi
  · intro a ha
    exact Nat.pos_of_ne_zero (data.padding_squarefree _ (hpairword a ha)).ne_zero
  · intro a ha
    exact data.tuple_squarefree _ (hpairword a ha)
  · intro a ha
    exact data.tuple_card _ (hpairword a ha)
  · intro y hy
    obtain ⟨a, b, hab, rfl⟩ := hy
    have ha : a.length ≤ R := by
      have hlen := congrArg List.length hab
      simp only [columnTupleWord, List.length_ofFn, List.length_append] at hlen
      omega
    have htake : (columnTupleWord w forward padding).take a.length = a := by
      rw [hab, List.take_left]
    have hv := havoid a.length ha
    change ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs)
      (n + wordDisplacement h ((columnTupleWord w forward padding).take a.length)) at hv
    rw [htake] at hv
    exact hv

end TwoPointCorrelations

end OAI
