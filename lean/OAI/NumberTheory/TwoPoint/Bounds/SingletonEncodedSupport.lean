import OAI.NumberTheory.TwoPoint.Bounds.ResidueWitnessHybrid
import OAI.NumberTheory.TwoPoint.Bounds.EncodedWitnessUnion
import OAI.NumberTheory.TwoPoint.Walks.WitnessRecordBounds

namespace OAI

/-! Nonzero singleton centering is supported on the finite encoded witness union. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def WitnessStepAdmissible (P Q : Finset ℕ) (J M : ℕ) (t : SignedStep) : Prop :=
  Squarefree t.tuple ∧ Squarefree t.padding ∧
    t.tuple.primeFactors.card ≤ J ∧ t.padding.primeFactors.card ≤ M ∧
    t.tuple.primeFactors ⊆ P ∧ t.padding.primeFactors ⊆ Q

theorem selected_residue_has_encoded_witness {ι W : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
    (S : Finset ι) (p : ι → ℕ) (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (B h s J n M D : ℕ) (P Q : Finset ℕ) (supply : ℕ → ℕ → Prop)
    (main : List SignedStep) (word : W → List SignedStep) (attachment : W → ℕ)
    (a x : ι → Fin B)
    (hatt : ∀ w, attachment w ≤ main.length)
    (hminimal : ∀ w, MinimalWord (ForwardProhibited h s supply) (word w))
    (hlen : ∀ w, (word w).length ≤ s)
    (hdivsq : ∀ w t, t ∈ word w → Squarefree (t.padding * t.tuple))
    (hcard : ∀ w t, t ∈ word w → t.tuple.primeFactors.card = J)
    (hsupport : ∀ w q j, TuplePrimeAt (word w) q j →
      ¬q ∣ h ∧ ∀ t ∈ word w, ¬q ∣ t.padding)
    (hpad : ∀ i ∈ S, ∀ w t, t ∈ word w → ¬p i ∣ t.padding)
    (hcover : ∀ w q, q ∈ wordDivisorPrimeSupport (word w) → ∃ i, p i = q)
    (position : S → ℕ)
    (hmain : ∀ i : S, ∀ v, TuplePrimeAt main (p i) v → v = position i)
    (hSmain : ∀ i ∈ S, p i ∈ wordDivisorPrimeSupport main)
    (hmainvalid : ∀ t ∈ main, WitnessStepAdmissible P Q J M t)
    (hwordvalid : ∀ w t, t ∈ word w → WitnessStepAdmissible P Q J M t)
    (hP : ∀ p ∈ P, p.Prime) (hPQ : Disjoint P Q)
    (hD : main.length + n * s ≤ D)
    (hnonzero : selectedMixedDifference S a
      (witnessAvoidance (fun w z => decide (AttachedResiduePositiveWord p h (word w)
        (wordDisplacement h (main.take (attachment w))) B z))) x ≠ 0)
    (hn : n * (s * J) < S.card) :
    ∃ R : Fin (D + 1), ∃ d : WitnessRecord n R.val,
      ∃ e : PrimeWordEncoding R.val (R.val * (J + M)) P Q,
        EncodedWitnessHybridEvent d e main p B h s J supply x := by
  have hsq (w) (t) (ht : t ∈ word w) := (hwordvalid w t ht).1
  obtain ⟨index, _hindex, hnum, y, hy, htests⟩ :=
    selected_residue_witnesses_and_hybrid S p hprime hinj B h s J n supply main word
      attachment a x hatt hminimal hlen hsq hdivsq hcard hsupport hpad hcover
      position hmain hnonzero hn
  let v := recordedWitnessWord main (fun i => word (index i))
  have hvlen : v.length ≤ D :=
    (recordedWitnessWord_length_le main (fun i => word (index i)) s
      (fun i => hlen (index i))).trans hD
  have hvalid (t) (ht : t ∈ v) : WitnessStepAdmissible P Q J M t := by
    rcases (mem_recordedWitnessWord main (fun i => word (index i)) t).mp ht with
      ht | ⟨i, hi⟩
    · exact hmainvalid t ht
    · exact hwordvalid (index i) t hi
  have hslots : Fintype.card (ActualPrimeSlot v.get) ≤ v.length * (J + M) := by
    exact recordedWitnessWord_slots_le main (fun i => word (index i)) J M
      (fun t ht => ⟨(hmainvalid t ht).2.2.1, (hmainvalid t ht).2.2.2.1⟩)
      (fun i t ht => ⟨(hwordvalid (index i) t ht).2.2.1,
        (hwordvalid (index i) t ht).2.2.2.1⟩)
  have hdisjoint (t) (ht : t ∈ v) (u) (hu : u ∈ v) :
      Disjoint t.tuple.primeFactors u.padding.primeFactors :=
    hPQ.mono (hvalid t ht).2.2.2.2.1 (hvalid u hu).2.2.2.2.2
  obtain ⟨d, e, he, hdecode, hem, hew, hea, heweight⟩ :=
    actual_witness_has_encoded_record main (fun i => word (index i))
      (fun i => attachment (index i)) (fun i => hatt (index i)) P Q (v.length * (J + M))
      h s J supply p hnum hslots (fun t ht => (hvalid t ht).1)
      (fun t ht => (hvalid t ht).2.1) (fun t ht => (hvalid t ht).2.2.2.2.1)
      (fun t ht => (hvalid t ht).2.2.2.2.2) hdisjoint hP
  refine ⟨⟨v.length, Nat.lt_succ_of_le hvlen⟩, d, e, he, ⟨hem, ?_, heweight⟩, y, ?_, ?_⟩
  · rw [hdecode]
    congr 1
    funext i
    simpa only [hdecode] using (hew i).symm
  · intro i hi
    exact hy i (fun his => hi (hSmain i his))
  · intro i
    rw [hew i, hea i]
    exact htests i

end TwoPointCorrelations

end OAI
