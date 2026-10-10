import OAI.NumberTheory.TwoPoint.Walks.WitnessSupport
import Mathlib.Data.Fin.Tuple.Sort

namespace OAI

/-! Private witnesses can be indexed by increasing attachment, including ties. -/

namespace TwoPointCorrelations

open Finset

lemma exists_monotone_enumeration {W : Type*} [Fintype W]
    (attachment : W → ℕ) (n : ℕ) (hcard : Fintype.card W = n) :
    ∃ e : Fin n ≃ W, Monotone (fun i => attachment (e i)) := by
  classical
  let e₀ : Fin n ≃ W := (Fintype.equivFinOfCardEq hcard).symm
  let f : Fin n → ℕ := fun i => attachment (e₀ i)
  exact ⟨(Tuple.sort f).trans e₀, Tuple.monotone_sort f⟩

/-- The cover is enumerated after selection, so sorting introduces no
factor counting all covering subfamilies or possible hybrid choices. -/
theorem ordered_numerical_witness_cover {ι W A : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
    (prime : ι → ℕ) (hinj : Function.Injective prime)
    (word : W → List SignedStep) (attachment : W → ℕ)
    (I : W → (ι → A) → Bool) (a x : ι → A)
    (hdepends : ∀ w, DependsOn (wordCoordinateSupport prime (word w)) (I w))
    (hnonzero : mixedDifference a (witnessAvoidance I) x ≠ 0)
    (s J T : ℕ) (hlen : ∀ w, (word w).length ≤ s)
    (hsq : ∀ w t, t ∈ word w → Squarefree t.tuple)
    (hcard : ∀ w t, t ∈ word w → t.tuple.primeFactors.card ≤ J)
    (hT : T * (s * J) < Fintype.card ι) :
    ∃ index : Fin T → W, Function.Injective index ∧
      Monotone (fun i => attachment (index i)) ∧ ∃ H : Finset ι,
      (∀ i, I (index i) (forceCoordinates H a x) = true) ∧
      ∃ mark : Fin T → ι, Function.Injective mark ∧
        ∀ i, (∃ r, TuplePrimeAt (word (index i)) (prime (mark i)) r) ∧
          ∀ j, j ≠ i → ¬∃ r, TuplePrimeAt (word (index j)) (prime (mark i)) r := by
  classical
  obtain ⟨R, hR, H, hI, mark, hmark, hprivate⟩ := numerical_witness_cover
    prime hinj word I a x hdepends hnonzero s J T hlen hsq hcard hT
  obtain ⟨e, he⟩ := exists_monotone_enumeration (fun i : R => attachment i.val) T
    (by simpa only [Fintype.card_coe] using hR)
  refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, he, H,
    fun i => hI (e i) (e i).property, fun i => mark (e i), hmark.comp e.injective, ?_⟩
  intro i
  refine ⟨(hprivate (e i)).1, ?_⟩
  intro j hji
  apply (hprivate (e i)).2 (e j) (e j).property
  exact fun hij => hji (e.injective (Subtype.ext hij))

end TwoPointCorrelations

end OAI
