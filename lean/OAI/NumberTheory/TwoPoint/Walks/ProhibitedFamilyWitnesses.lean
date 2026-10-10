import OAI.NumberTheory.TwoPoint.Walks.ProhibitedDensity
import OAI.NumberTheory.TwoPoint.Bounds.SingletonEncodedSupport

namespace OAI

/-! The literal minimal-word catalog discharges the numerical witness-family hypotheses. -/

namespace TwoPointCorrelations.ProhibitedPrimeFamily

open Finset
open scoped Classical

variable {h J M : ℕ} (F : ProhibitedPrimeFamily h J M)

lemma catalog_pairs (s : ℕ) (c : ProhibitedCatalog F.pairs h s)
    (t : SignedStep) (ht : t ∈ decodeStepWord c.val) : (t.tuple, t.padding) ∈ F.pairs :=
  c.property.1.2.2.1 t ht

lemma catalog_admissible (s : ℕ) (c : ProhibitedCatalog F.pairs h s)
    (t : SignedStep) (ht : t ∈ decodeStepWord c.val) : WitnessStepAdmissible F.P F.Q J M t := by
  have hp := F.catalog_pairs s c t ht
  exact ⟨F.tuple_squarefree _ hp, F.padding_squarefree _ hp,
    (F.tuple_card _ hp).le, F.padding_card _ hp, F.tuple_pool _ hp, F.padding_pool _ hp⟩

lemma catalog_whole_squarefree (s : ℕ) (c : ProhibitedCatalog F.pairs h s)
    (t : SignedStep) (ht : t ∈ decodeStepWord c.val) : Squarefree (t.padding * t.tuple) :=
  F.whole_squarefree _ (F.catalog_pairs s c t ht)

lemma catalog_tuple_card (s : ℕ) (c : ProhibitedCatalog F.pairs h s)
    (t : SignedStep) (ht : t ∈ decodeStepWord c.val) : t.tuple.primeFactors.card = J :=
  F.tuple_card _ (F.catalog_pairs s c t ht)

lemma catalog_prime_support (s : ℕ) (c : ProhibitedCatalog F.pairs h s)
    (q v : ℕ) (hq : TuplePrimeAt (decodeStepWord c.val) q v) :
    ¬q ∣ h ∧ ∀ t ∈ decodeStepWord c.val, ¬q ∣ t.padding := by
  obtain ⟨hqprime, t, ht, hqt⟩ := hq
  have htpairs := F.catalog_pairs s c t (List.mem_of_getElem? ht)
  have hqP : q ∈ F.P := F.tuple_pool _ htpairs
    (hqprime.mem_primeFactors hqt (F.tuple_squarefree _ htpairs).ne_zero)
  refine ⟨F.excluded q hqP, ?_⟩
  intro a ha hqa
  have hapairs := F.catalog_pairs s c a ha
  have hqQ : q ∈ F.Q := F.padding_pool _ hapairs
    (hqprime.mem_primeFactors hqa (F.padding_squarefree _ hapairs).ne_zero)
  exact disjoint_left.mp F.disjoint hqP hqQ

lemma catalog_padding_excluded (s : ℕ) (c : ProhibitedCatalog F.pairs h s)
    (q : ℕ) (hq : q ∈ F.P) (t : SignedStep) (ht : t ∈ decodeStepWord c.val) :
    ¬q ∣ t.padding := by
  intro hd
  have hpairs := F.catalog_pairs s c t ht
  have hqQ : q ∈ F.Q := F.padding_pool _ hpairs
    ((F.primeP q hq).mem_primeFactors hd (F.padding_squarefree _ hpairs).ne_zero)
  exact disjoint_left.mp F.disjoint hq hqQ

end TwoPointCorrelations.ProhibitedPrimeFamily

end OAI
