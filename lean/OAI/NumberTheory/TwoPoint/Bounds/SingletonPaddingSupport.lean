import OAI.NumberTheory.TwoPoint.Bounds.SingletonEncodedSupport
import OAI.NumberTheory.TwoPoint.Bounds.EncodedPaddingWitness
import OAI.NumberTheory.TwoPoint.Bounds.ForcedSingletonDifference

namespace OAI

/-! The selected singleton support retains the original padding event. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem selected_residue_has_padding_witness {ι W : Type*}
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
    (V : Finset ι) (hSV : S ⊆ V) (hretain : RetainedMainTests p V h B main x)
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
        EncodedPaddingWitnessEvent V d e main p B h s J supply x := by
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
  refine ⟨⟨v.length, Nat.lt_succ_of_le hvlen⟩, d, e, he, ⟨hem, ?_, heweight⟩, hretain, y, ?_, ?_⟩
  · rw [hdecode]
    congr 1
    funext i
    simpa only [hdecode] using (hew i).symm
  · intro i hi
    exact hy i (fun his => hi (hSV his))
  · intro i
    rw [hew i, hea i]
    exact htests i

theorem forced_selected_residue_has_padding_witness {ι W : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
    (S : Finset ι) (p : ι → ℕ) (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (B h s J n M D : ℕ) (P Q : Finset ℕ) (supply : ℕ → ℕ → Prop)
    (main : List SignedStep) (word : W → List SignedStep) (attachment : W → ℕ)
    (a b x : ι → Fin B) (lit : Finset ι) (hSlit : Disjoint S lit)
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
    (V : Finset ι) (hSV : S ⊆ V) (hlitV : lit ⊆ V)
    (hretain : RetainedMainTests p V h B main x)
    (hmainvalid : ∀ t ∈ main, WitnessStepAdmissible P Q J M t)
    (hwordvalid : ∀ w t, t ∈ word w → WitnessStepAdmissible P Q J M t)
    (hP : ∀ p ∈ P, p.Prime) (hPQ : Disjoint P Q)
    (hD : main.length + n * s ≤ D)
    (hnonzero : selectedMixedDifference S a
      (fun z => witnessAvoidance (fun w y => decide (AttachedResiduePositiveWord p h (word w)
        (wordDisplacement h (main.take (attachment w))) B y)) (forceCoordinates lit b z)) x ≠ 0)
    (hn : n * (s * J) < S.card) :
    ∃ R : Fin (D + 1), ∃ d : WitnessRecord n R.val,
      ∃ e : PrimeWordEncoding R.val (R.val * (J + M)) P Q,
        EncodedPaddingWitnessEvent V d e main p B h s J supply x := by
  let F : (ι → Fin B) → ℝ := witnessAvoidance (fun w z => decide
    (AttachedResiduePositiveWord p h (word w)
      (wordDisplacement h (main.take (attachment w))) B z))
  have hnz : selectedMixedDifference S a F (forceCoordinates lit b x) ≠ 0 := by
    rw [← selectedMixedDifference_force_disjoint S lit hSlit a b x F]
    exact hnonzero
  have hsame : ∀ i, i ∉ V → forceCoordinates lit b x i = x i := by
    intro i hi
    have hilit : i ∉ lit := fun hilit => hi (hlitV hilit)
    simp only [forceCoordinates_apply, hilit, ite_false]
  have hretain' : RetainedMainTests p V h B main (forceCoordinates lit b x) :=
    (retainedMainTests_congr p V h B main _ x hsame).mpr hretain
  obtain ⟨R, d, e, he⟩ := selected_residue_has_padding_witness S p hprime hinj
    B h s J n M D P Q supply main word attachment a (forceCoordinates lit b x)
    hatt hminimal hlen hdivsq hcard hsupport hpad hcover position hmain V hSV hretain'
    hmainvalid hwordvalid hP hPQ hD hnz hn
  exact ⟨R, d, e, (EncodedPaddingWitnessEvent.congr V d e main p B h s J supply
    (forceCoordinates lit b x) x hsame).mp he⟩

end TwoPointCorrelations

end OAI
