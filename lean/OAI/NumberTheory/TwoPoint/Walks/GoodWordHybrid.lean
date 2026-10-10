import OAI.NumberTheory.TwoPoint.Walks.SelectedGoodHybrid
import OAI.NumberTheory.TwoPoint.Bounds.CatalogVertexIndicator
import OAI.NumberTheory.TwoPoint.Walks.TuplePerfectRows
import OAI.NumberTheory.TwoPoint.Bounds.MainPaddingTests

namespace OAI

/-! A surviving weighted mixed difference supplies the exact integer word needed by the forest cover. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem good_word_integer_hybrid {h J M B s D m : ℕ}
    (data : ProhibitedPrimeFamily h J M) (step : Fin m → SignedStep)
    (hstep : ∀ i, ((step i).tuple, (step i).padding) ∈ data.pairs)
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (hmD : m ≤ D)
    (label : Fin m × Fin J → ↥(data.P ∪ data.Q))
    (hlabels : ∀ i (p : ↥(data.P ∪ data.Q)), p.val ∈ (step i).tuple.primeFactors →
      ∃ j, label (i, j) = p)
    (U : Finset (Fin m × Fin J)) (base x : ↥(data.P ∪ data.Q) → Fin B)
    (weight : (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (hweight : ∀ y z, (∀ i, i ∉ univ.image label → y i = z i) → weight y = weight z)
    (hpadding : ∀ y, weight y ≠ 0 → MainPaddingTests
      (fun p : ↥(data.P ∪ data.Q) => p.val) h B (List.ofFn step) y)
    (hx : weight x ≠ 0)
    (hL : LitConsistent (nonsingletonSlots label \ U) label
      (fun t => forcedResidue B (label t).val (data.prime _).pos (hB _ (label t).property)
        (wordDisplacement h ((List.ofFn step).take t.1.val))))
    (hnz : selectedMixedDifference (singletonLabels label)
      (singletonTarget label
        (fun t => forcedResidue B (label t).val (data.prime _).pos (hB _ (label t).property)
          (wordDisplacement h ((List.ofFn step).take t.1.val))) base)
      (fun z => attachedCatalogAvoidance data s B D (List.ofFn step)
        (forceCoordinates ((nonsingletonSlots label \ U).image label)
          (litForcedTarget (nonsingletonSlots label \ U) label
            (fun t => forcedResidue B (label t).val (data.prime _).pos (hB _ (label t).property)
              (wordDisplacement h ((List.ofFn step).take t.1.val))) base) z)) x ≠ 0) :
    ∃ n : ℤ,
      (∀ i ∈ perfectRows label U, (step i).divisor ∣
        n + wordDisplacement h ((List.ofFn step).take i.val)) ∧
      (∀ v ≤ m, ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs)
        (n + wordDisplacement h ((List.ofFn step).take v))) := by
  let main := List.ofFn step
  let target (t : Fin m × Fin J) := forcedResidue B (label t).val (data.prime _).pos
    (hB _ (label t).property) (wordDisplacement h (main.take t.1.val))
  obtain ⟨y, _hy, hylit, hyw, hyG⟩ := centered_word_nonzero_hybrid label target base x U
    (attachedCatalogAvoidance data s B D main) weight hweight hL hnz
  have hypad := hpadding y (fun hzero => hx (hyw.symm.trans hzero))
  let (p : ↥(data.P ∪ data.Q)) : NeZero p.val := ⟨(data.prime p).ne_zero⟩
  have hcop : Pairwise (fun p q : ↥(data.P ∪ data.Q) => p.val.Coprime q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (data.prime p) (data.prime q)).mpr
      (fun he => hpq (Subtype.ext he))
  obtain ⟨n, hn⟩ := exists_common_integer_residue (fun p : ↥(data.P ∪ data.Q) => p.val)
    hcop (fun p => ((y p).val : ZMod p.val))
  refine ⟨n, ?_, ?_⟩
  · intro i hi
    have hsquare := data.whole_squarefree _ (hstep i)
    have htests : ∀ q ∈ ((step i).padding * (step i).tuple).primeFactors,
        (q : ℤ) ∣ n + wordDisplacement h (main.take i.val) := by
      intro q hq
      have hq' := hq
      rw [Nat.primeFactors_mul (data.padding_squarefree _ (hstep i)).ne_zero
        (data.tuple_squarefree _ (hstep i)).ne_zero, mem_union] at hq'
      have hqpool : q ∈ data.P ∪ data.Q := by
        rcases hq' with hpad | htup
        · exact mem_union_right _ (data.padding_pool _ (hstep i) hpad)
        · exact mem_union_left _ (data.tuple_pool _ (hstep i) htup)
      let c : ↥(data.P ∪ data.Q) := ⟨q, hqpool⟩
      apply (residue_offset_divisibility (((y c).val : ZMod c.val)) n
        (wordDisplacement h (main.take i.val)) (hn c)).mpr
      rcases hq' with hpad | htup
      · have hk : i.val < main.length := by simpa only [main, List.length_ofFn] using i.isLt
        have ht := hypad (⟨i.val, hk⟩ : Fin main.length) c
        have he : main.get ⟨i.val, hk⟩ = step i := by simp [main, List.get_eq_getElem]
        have hpad' : c.val ∈ (main.get ⟨i.val, hk⟩).padding.primeFactors := by
          simpa only [he] using hpad
        exact ht hpad'
      · obtain ⟨j, hj⟩ := hlabels i c htup
        have hyl := hylit (i, j) (perfectRows_lit label U i hi j)
        rw [hj] at hyl
        rw [hyl]
        dsimp [target]
        rw [hj]
        exact ZMod.natCast_zmod_val
          (-(wordDisplacement h (main.take i.val) : ZMod c.val))
    have hd := (squarefree_divisor_iff ((step i).padding * (step i).tuple) hsquare
      (n + wordDisplacement h (main.take i.val))).mpr htests
    simpa only [SignedStep.divisor, Nat.cast_mul] using hd
  · have hmainD : main.length ≤ D := by simpa only [main, List.length_ofFn] using hmD
    have havoid := (attachedCatalogAvoidance_ne_zero_iff data s B D main hmainD y n hn).mp hyG
    simpa only [main, List.length_ofFn] using havoid

end TwoPointCorrelations

end OAI
