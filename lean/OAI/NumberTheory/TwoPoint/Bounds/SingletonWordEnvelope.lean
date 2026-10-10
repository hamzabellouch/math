import OAI.NumberTheory.TwoPoint.Walks.WeightedWordEnvelope
import OAI.NumberTheory.TwoPoint.Bounds.SingletonPaddingSupport

namespace OAI

/-! Every nonzero full-word envelope supplies the same bounded numerical witness record. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem singleton_envelope_has_padding_witness {ι τ W : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype τ] [Fintype W] [DecidableEq W]
    (label : τ → ι) (p : ι → ℕ) (hprime : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (B h s J n M D : ℕ)
    (P Q : Finset ℕ) (supply : ℕ → ℕ → Prop)
    (main : List SignedStep) (word : W → List SignedStep) (attachment : W → ℕ)
    (target : τ → Fin B) (base x : ι → Fin B) (R : (ι → Fin B) → ℝ)
    (hatt : ∀ w, attachment w ≤ main.length)
    (hminimal : ∀ w, MinimalWord (ForwardProhibited h s supply) (word w))
    (hlen : ∀ w, (word w).length ≤ s)
    (hdivsq : ∀ w t, t ∈ word w → Squarefree (t.padding * t.tuple))
    (hcard : ∀ w t, t ∈ word w → t.tuple.primeFactors.card = J)
    (hsupport : ∀ w q j, TuplePrimeAt (word w) q j →
      ¬q ∣ h ∧ ∀ t ∈ word w, ¬q ∣ t.padding)
    (hpad : ∀ i ∈ singletonLabels label, ∀ w t, t ∈ word w → ¬p i ∣ t.padding)
    (hcover : ∀ w q, q ∈ wordDivisorPrimeSupport (word w) → ∃ i, p i = q)
    (position : singletonLabels label → ℕ)
    (hmain : ∀ i : singletonLabels label, ∀ v, TuplePrimeAt main (p i) v → v = position i)
    (hretain : R x ≠ 0 → RetainedMainTests p (univ.image label) h B main x)
    (hmainvalid : ∀ t ∈ main, WitnessStepAdmissible P Q J M t)
    (hwordvalid : ∀ w t, t ∈ word w → WitnessStepAdmissible P Q J M t)
    (hP : ∀ q ∈ P, q.Prime) (hPQ : Disjoint P Q)
    (hD : main.length + n * s ≤ D)
    (hn : n * (s * J) < (singletonLabels label).card)
    (hne : centeredWordEnvelope label target base R
      (witnessAvoidance (fun w z => decide (AttachedResiduePositiveWord p h (word w)
        (wordDisplacement h (main.take (attachment w))) B z))) x ≠ 0) :
    ∃ r : Fin (D + 1), ∃ d : WitnessRecord n r.val,
      ∃ e : PrimeWordEncoding r.val (r.val * (J + M)) P Q,
        EncodedPaddingWitnessEvent (univ.image label) d e main p B h s J supply x := by
  obtain ⟨U, _hU, _hL, hRx, hd⟩ := centeredWordEnvelope_ne_zero label target base R _ x hne
  have hS : singletonLabels label ⊆ univ.image label := by
    intro i hi
    obtain ⟨t, ht⟩ := singleton_occurrence_exists label ⟨i, hi⟩
    exact mem_image.mpr ⟨t, mem_univ _, ht⟩
  have hlit : (nonsingletonSlots label \ U).image label ⊆ univ.image label := by
    intro i hi
    obtain ⟨t, _, ht⟩ := mem_image.mp hi
    exact mem_image.mpr ⟨t, mem_univ _, ht⟩
  exact forced_selected_residue_has_padding_witness (singletonLabels label) p hprime hinj
    B h s J n M D P Q supply main word attachment (singletonTarget label target base)
    (litForcedTarget (nonsingletonSlots label \ U) label target base) x
    ((nonsingletonSlots label \ U).image label) (singleton_disjoint_designated label U)
    hatt hminimal hlen hdivsq hcard hsupport hpad hcover position hmain
    (univ.image label) hS hlit (hretain hRx) hmainvalid hwordvalid hP hPQ hD hd hn

end TwoPointCorrelations

end OAI
