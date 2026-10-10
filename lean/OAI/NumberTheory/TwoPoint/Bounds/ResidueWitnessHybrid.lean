import OAI.NumberTheory.TwoPoint.Bounds.ResidueNumericalWitnesses

namespace OAI

/-! Keep the same common hybrid that supplies the numerical witnesses. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem selected_residue_witnesses_and_hybrid {ι W : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
    (S : Finset ι) (p : ι → ℕ) (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (B h s J T : ℕ) (supply : ℕ → ℕ → Prop)
    (main : List SignedStep) (word : W → List SignedStep) (attachment : W → ℕ)
    (a x : ι → Fin B)
    (hatt : ∀ w, attachment w ≤ main.length)
    (hminimal : ∀ w, MinimalWord (ForwardProhibited h s supply) (word w))
    (hlen : ∀ w, (word w).length ≤ s)
    (hsq : ∀ w t, t ∈ word w → Squarefree t.tuple)
    (hdivsq : ∀ w t, t ∈ word w → Squarefree (t.padding * t.tuple))
    (hcard : ∀ w t, t ∈ word w → t.tuple.primeFactors.card = J)
    (hsupport : ∀ w q j, TuplePrimeAt (word w) q j →
      ¬q ∣ h ∧ ∀ t ∈ word w, ¬q ∣ t.padding)
    (hpad : ∀ i ∈ S, ∀ w t, t ∈ word w → ¬p i ∣ t.padding)
    (hcover : ∀ w q, q ∈ wordDivisorPrimeSupport (word w) → ∃ i, p i = q)
    (position : S → ℕ)
    (hmain : ∀ i : S, ∀ v, TuplePrimeAt main (p i) v → v = position i)
    (hnonzero : selectedMixedDifference S a
      (witnessAvoidance (fun w z => decide (AttachedResiduePositiveWord p h (word w)
        (wordDisplacement h (main.take (attachment w))) B z))) x ≠ 0)
    (hT : T * (s * J) < S.card) :
    ∃ index : Fin T → W, Function.Injective index ∧
      NumericalWitnessEvent main (fun i => word (index i)) p h s J supply ∧
      ∃ y : ι → Fin B, (∀ i, i ∉ S → y i = x i) ∧
        ∀ i, AttachedResiduePositiveWord p h (word (index i))
          (wordDisplacement h (main.take (attachment (index i)))) B y := by
  let I : W → (S → Fin B) → Bool := fun w z => decide
    (AttachedResiduePositiveWord p h (word w)
      (wordDisplacement h (main.take (attachment w))) B
      (joinCoordinates S z (fun i => x i)))
  have hdepends (w) : DependsOn (wordCoordinateSupport (fun i : S => p i) (word w)) (I w) :=
    attached_residue_test_depends S p h B (word w) _ (hsq w)
      (fun i _ => hprime i) (fun i hi => hpad i hi w) _
  have hn : mixedDifference (fun i : S => a i) (witnessAvoidance I) (fun i : S => x i) ≠ 0 :=
    hnonzero
  obtain ⟨index, hindex, horder, H, hI, mark, _hmark, hprivate⟩ :=
    ordered_numerical_witness_cover (fun i : S => p i) (hinj.comp Subtype.val_injective)
      word attachment I (fun i : S => a i) (fun i : S => x i) hdepends hn s J T hlen hsq
      (fun w t ht => (hcard w t ht).le) (by simpa only [Fintype.card_coe] using hT)
  let hybrid := joinCoordinates S (forceCoordinates H (fun i : S => a i) (fun i : S => x i))
    (fun i => x i)
  have htests (i : Fin T) : AttachedResiduePositiveWord p h (word (index i))
      (wordDisplacement h (main.take (attachment (index i)))) B hybrid := by
    have hi := hI i
    exact of_decide_eq_true hi
  obtain ⟨origin, horigin⟩ := attached_residue_words_common_origin T B h p hprime hinj hybrid
    (fun i => word (index i)) (fun i => wordDisplacement h (main.take (attachment (index i))))
    (fun i => hdivsq (index i)) (fun i => hcover (index i)) htests
  refine ⟨index, hindex, ?_, hybrid, ?_, htests⟩
  · refine ⟨(fun i => (mark i).val), (fun i => attachment (index i)),
      (fun i => position (mark i)), horder, (fun i => hatt (index i)), hinj, hprime,
      (fun i => hminimal (index i)), (fun i => hsq (index i)), (fun i => hcard (index i)),
      (fun i => hsupport (index i)), ?_, ?_, ?_, origin, horigin⟩
    · intro i
      exact (mem_wordPrimeSupport_iff _ _ (hsq (index i))).mpr (hprivate i).1
    · intro i j hji hmem
      exact (hprivate i).2 j hji ((mem_wordPrimeSupport_iff _ _ (hsq (index j))).mp hmem)
    · intro i v hv
      exact hmain (mark i) v hv
  · intro i hi
    simp only [hybrid, joinCoordinates, hi, dite_false]

end TwoPointCorrelations

end OAI
