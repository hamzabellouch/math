import Mathlib

namespace OAI

universe u_Ω u_A u_I

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem310.ExposureUnionBound

/-- Averaging conditional bounds over a finite exposure does not introduce a
factor for the number of possible exposure values. The event itself need not
be measurable, since the proof uses only outer-measure subadditivity. -/
theorem measure_le_of_finite_exposure
    {Ω : Type u_Ω} {A : Type u_A} [MeasurableSpace Ω] [Fintype A]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → A) (hf : ∀ a, MeasurableSet {ω | f ω = a})
    (E : Set Ω) (good : Set A) (badBound goodBound : ENNReal)
    (hbad : μ {ω | f ω ∉ good} ≤ badBound)
    (hgood : ∀ a ∈ good,
      μ (E ∩ {ω | f ω = a}) ≤ goodBound * μ {ω | f ω = a}) :
    μ E ≤ badBound + goodBound := by
  classical
  let localEvent : A → Set Ω := fun a =>
    if a ∈ good then E ∩ {ω | f ω = a} else ∅
  have hcover : E ⊆ {ω | f ω ∉ good} ∪ ⋃ a, localEvent a := by
    intro ω hω
    by_cases hg : f ω ∈ good
    · right
      exact Set.mem_iUnion.mpr ⟨f ω, by simp [localEvent, hg, hω]⟩
    · exact Or.inl hg
  have hlocal (a : A) : μ (localEvent a) ≤ goodBound * μ {ω | f ω = a} := by
    by_cases ha : a ∈ good
    · simpa [localEvent, ha] using hgood a ha
    · simp [localEvent, ha]
  have hmass : (∑ a : A, μ {ω | f ω = a}) = 1 := by
    have h := sum_measure_preimage_singleton (μ := μ) (Finset.univ : Finset A)
      (f := f) (fun a _ => hf a)
    simpa [Set.preimage] using h
  calc
    μ E ≤ μ ({ω | f ω ∉ good} ∪ ⋃ a, localEvent a) := measure_mono hcover
    _ ≤ μ {ω | f ω ∉ good} + μ (⋃ a, localEvent a) := measure_union_le _ _
    _ ≤ badBound + ∑ a : A, μ (localEvent a) :=
      add_le_add hbad (measure_iUnion_fintype_le μ localEvent)
    _ ≤ badBound + ∑ a : A, goodBound * μ {ω | f ω = a} :=
      add_le_add le_rfl (Finset.sum_le_sum fun a _ => hlocal a)
    _ = badBound + goodBound := by rw [← Finset.mul_sum, hmass, mul_one]

/-- A finite family of trial failures yields a mass-weighted bound on one
exposure atom. This formulation avoids dividing by the atom probability. -/
theorem measure_inter_le_of_finite_cover
    {Ω : Type u_Ω} {I : Type u_I} [MeasurableSpace Ω]
    (μ : Measure Ω) (E atom : Set Ω) (R : Finset I) (F : I → Set Ω)
    (q : ENNReal)
    (hcover : E ∩ atom ⊆ ⋃ i ∈ R, F i ∩ atom)
    (htrial : ∀ i ∈ R, μ (F i ∩ atom) ≤ q * μ atom) :
    μ (E ∩ atom) ≤ (R.card : ENNReal) * q * μ atom := by
  calc
    μ (E ∩ atom) ≤ μ (⋃ i ∈ R, F i ∩ atom) := measure_mono hcover
    _ ≤ ∑ i ∈ R, μ (F i ∩ atom) := measure_biUnion_finset_le R _
    _ ≤ ∑ _i ∈ R, q * μ atom := Finset.sum_le_sum htrial
    _ = (R.card : ENNReal) * q * μ atom := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact (mul_assoc _ _ _).symm

/-- The raw-failure estimate: an exceptional exposure has mass at most `p`,
and on every other exposure a finite union bound has conditional mass at most
`p`. The final estimate is `2*p`, irrespective of the number of atoms. -/
theorem measure_le_two_mul_of_exposure_covers
    {Ω : Type u_Ω} {A : Type u_A} {I : Type u_I} [MeasurableSpace Ω] [Fintype A]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → A) (hf : ∀ a, MeasurableSet {ω | f ω = a})
    (E : Set Ω) (good : Set A) (R : A → Finset I)
    (F : A → I → Set Ω) (q : A → ENNReal) (p : ENNReal)
    (hbad : μ {ω | f ω ∉ good} ≤ p)
    (hcover : ∀ a ∈ good,
      E ∩ {ω | f ω = a} ⊆ ⋃ i ∈ R a, F a i ∩ {ω | f ω = a})
    (htrial : ∀ a ∈ good, ∀ i ∈ R a,
      μ (F a i ∩ {ω | f ω = a}) ≤ q a * μ {ω | f ω = a})
    (hbudget : ∀ a ∈ good, ((R a).card : ENNReal) * q a ≤ p) :
    μ E ≤ 2 * p := by
  have hlocal (a : A) (ha : a ∈ good) :
      μ (E ∩ {ω | f ω = a}) ≤ p * μ {ω | f ω = a} := by
    exact (measure_inter_le_of_finite_cover μ E {ω | f ω = a}
      (R a) (F a) (q a) (hcover a ha) (htrial a ha)).trans
        (mul_le_mul_left (hbudget a ha) _)
  simpa only [two_mul] using
    measure_le_of_finite_exposure μ f hf E good p p hbad hlocal

end Problem310.ExposureUnionBound

end

end OAI
