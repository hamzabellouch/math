import OAI.NumberTheory.TwoPoint.Walks.ColumnWordGeometry

namespace OAI

/-! The perfect-block geometry for the actual labels of a fixed prime column. -/

namespace TwoPointCorrelations.ColumnWordPattern

open Finset

variable {α : Type*}

/-- Disjoint column supplies turn numerical prime intervals into intervals
of the abstract labels used by the decoder. -/
theorem label_intervals_of_prime_intervals (w : ColumnWordPattern α) (value : α → ℕ)
    (hvalue : Function.Injective value) (hprime : ∀ z, (value z).Prime)
    (hother : ∀ z t, t < w.length → ¬value z ∣ w.otherColumns t)
    (hinterval : TuplePrimeIntervals (w.word value)) :
    ∀ i j k : Fin w.length, i ≤ j → j ≤ k → w.label i = w.label k → w.label j = w.label i := by
  have hmem (i : Fin w.length) : TuplePrimeAt (w.word value) (value (w.label i)) i := by
    apply (tuplePrimeAt_iff_getElem _ _ i (by simp)).mpr
    refine ⟨hprime _, ?_⟩
    simp [word, step]
  intro i j k hij hjk heq
  have hpk : TuplePrimeAt (w.word value) (value (w.label i)) k := by
    simpa only [heq] using hmem k
  have hpj := hinterval (value (w.label i)) i j k hij hjk (by simp) (hmem i) hpk
  have hdiv := ((tuplePrimeAt_iff_getElem _ _ j (by simp)).mp hpj).2
  simp only [word, List.getElem_ofFn, step] at hdiv
  have hval : value (w.label i) ∣ value (w.label j) :=
    ((hprime _).dvd_mul.mp hdiv).resolve_right (hother _ j j.isLt)
  have he : value (w.label i) = value (w.label j) :=
    (Nat.dvd_prime (hprime _)).mp hval |>.resolve_left (hprime _).ne_one
  exact hvalue he.symm

/-- All block geometry needed for coding follows from the genuine surviving
positive-word lemma, with only the disjoint prime-supply data added. -/
theorem positive_block_geometry (w : ColumnWordPattern α) (value : α → ℕ)
    (hvalue : Function.Injective value) (hprime : ∀ z, (value z).Prime)
    (hother : ∀ z t, t < w.length → ¬value z ∣ w.otherColumns t)
    {h s J : ℕ} {supply : ℕ → ℕ → Prop} {x : ℤ}
    (hw : PositiveWord h x (w.word value)) (hh : 0 < h)
    (hlen : w.length ≤ s)
    (heligible : ∀ a ∈ w.word value, supply a.tuple a.padding)
    (hq : ∀ a ∈ w.word value, 0 < a.padding)
    (hsq : ∀ a ∈ w.word value, Squarefree a.tuple)
    (hcard : ∀ a ∈ w.word value, a.tuple.primeFactors.card = J)
    (hchain : (w.word value).IsChain (fun a b => a.tuple ≠ b.tuple))
    (hsupport : ∀ p j, TuplePrimeAt (w.word value) p j →
      ¬p ∣ h ∧ ∀ a ∈ w.word value, ¬p ∣ a.padding)
    (hsurvive : ∀ y, WordVertex h x (w.word value) y → ¬ProhibitedSite h s supply y) :
    (∀ i j k : Fin w.length, i ≤ j → j ≤ k → w.label i = w.label k → w.label j = w.label i) ∧
      ∀ a b z, a < b → b ≤ w.length →
        (∀ t ∈ Ico a b, w.label t = z) →
        (∑ t ∈ Ico a b, (w.coefficient h t : ℝ)) ≠ 0 := by
  have hg := hw.block_geometry hh (by simpa using hlen) heligible hq hsq hcard hchain hsupport hsurvive
  refine ⟨w.label_intervals_of_prime_intervals value hvalue hprime hother hg.1, ?_⟩
  intro a b z hab hb hconst
  exact w.constant_run_real_coefficient_ne_zero h value a b hab.le hb z hconst
    (hg.2 a b hab (by simpa using hb))

end TwoPointCorrelations.ColumnWordPattern

end OAI
