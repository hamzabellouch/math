import OAI.NumberTheory.TwoPoint.Walks.WitnessOrdering
import OAI.NumberTheory.TwoPoint.Bounds.PartialCentering

namespace OAI

/-! Apply the witness-cover argument only to the centered singleton coordinates. -/

namespace TwoPointCorrelations

open Finset

variable {ι W A : Type*} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]

omit [Fintype W] [DecidableEq W] in
/-- Freeze every coordinate outside the selected singleton set. Dependence
on actual prime support restricts to the corresponding singleton support. -/
lemma word_dependsOn_restrict (S : Finset ι) (prime : ι → ℕ)
    (word : List SignedStep) (I : (ι → A) → Bool)
    (hI : DependsOn (wordCoordinateSupport prime word) I)
    (outside : {i // i ∉ S} → A) :
    DependsOn (wordCoordinateSupport (fun i : S => prime i) word)
      (fun z : S → A => I (joinCoordinates S z outside)) := by
  intro z z' hzz
  apply hI
  intro i hi
  by_cases his : i ∈ S
  · have hz := hzz ⟨i, his⟩ (by
      simpa only [wordCoordinateSupport, mem_filter, mem_univ, true_and] using
        (mem_filter.mp hi).2)
    simpa only [joinCoordinates, dite_eq_left his] using hz
  · simp only [joinCoordinates, dite_eq_right his]

/-- Nonzero selected centering yields a single hybrid containing the
ordered family of witnesses. No extra choices of outside coordinates or
independent hybrid draws are introduced. -/
theorem selected_ordered_numerical_witness_cover
    (S : Finset ι) (prime : ι → ℕ) (hinj : Function.Injective prime)
    (word : W → List SignedStep) (attachment : W → ℕ)
    (I : W → (ι → A) → Bool) (a x : ι → A)
    (hdepends : ∀ w, DependsOn (wordCoordinateSupport prime (word w)) (I w))
    (hnonzero : selectedMixedDifference S a (witnessAvoidance I) x ≠ 0)
    (s J T : ℕ) (hlen : ∀ w, (word w).length ≤ s)
    (hsq : ∀ w t, t ∈ word w → Squarefree t.tuple)
    (hcard : ∀ w t, t ∈ word w → t.tuple.primeFactors.card ≤ J)
    (hT : T * (s * J) < S.card) :
    ∃ index : Fin T → W, Function.Injective index ∧
      Monotone (fun i => attachment (index i)) ∧ ∃ H : Finset S,
      (∀ i, I (index i) (joinCoordinates S
        (forceCoordinates H (fun j : S => a j) (fun j : S => x j))
        (fun j : {j // j ∉ S} => x j)) = true) ∧
      ∃ mark : Fin T → S, Function.Injective mark ∧
        ∀ i, (∃ r, TuplePrimeAt (word (index i)) (prime (mark i)) r) ∧
          ∀ j, j ≠ i → ¬∃ r, TuplePrimeAt (word (index j)) (prime (mark i)) r := by
  let outside : {i // i ∉ S} → A := fun i => x i
  let tests : W → (S → A) → Bool := fun w z => I w (joinCoordinates S z outside)
  have htests (w : W) :
      DependsOn (wordCoordinateSupport (fun i : S => prime i) (word w)) (tests w) :=
    word_dependsOn_restrict S prime (word w) (I w) (hdepends w) outside
  have hn : mixedDifference (fun i : S => a i) (witnessAvoidance tests)
      (fun i : S => x i) ≠ 0 := hnonzero
  exact ordered_numerical_witness_cover (fun i : S => prime i)
    (hinj.comp Subtype.val_injective) word attachment tests
    (fun i : S => a i) (fun i : S => x i) htests hn s J T hlen hsq hcard
    (by simpa only [Fintype.card_coe] using hT)

end TwoPointCorrelations

end OAI
