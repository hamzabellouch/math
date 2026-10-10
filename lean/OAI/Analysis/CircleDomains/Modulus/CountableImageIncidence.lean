import OAI.Analysis.CircleDomains.Topology.ResidualClosedIntervals

namespace OAI

/-! Incidence bounds for the countable image exposed by discarded constant
tags. The estimate charges parameter times, and hence retains multiplicity. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {T X Z : Type*}

def timeIncidence (R : Set (Z × X)) (γ : T → X) (A : Set T) : Set Z :=
  {z | ∃ t ∈ A, (z, γ t) ∈ R}

def timeToll (γ : T → X) (A : Set T) (m : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' t : A, m (γ t)

theorem timeToll_eq_indicator (γ : T → X) (A : Set T) (m : X → ℝ≥0∞) :
    timeToll γ A m = ∑' t, if t ∈ A then m (γ t) else 0 := by
  exact tsum_subtype A (fun t => m (γ t))

theorem timeIncidence_iUnion {ι : Type*} (R : Set (Z × X)) (γ : T → X)
    (A : ι → Set T) : timeIncidence R γ (⋃ i, A i) = ⋃ i, timeIncidence R γ (A i) := by
  ext z
  simp only [timeIncidence, mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨t, ⟨i, hi⟩, ht⟩
    exact ⟨i, t, hi, ht⟩
  · rintro ⟨i, t, hi, ht⟩
    exact ⟨t, ⟨i, hi⟩, ht⟩

theorem timeToll_mono (γ : T → X) (m : X → ℝ≥0∞) {A C : Set T}
    (h : A ⊆ C) : timeToll γ A m ≤ timeToll γ C m :=
  ENNReal.tsum_mono_subtype (fun t => m (γ t)) h

theorem timeToll_iUnion {ι : Type*} (γ : T → X) (m : X → ℝ≥0∞)
    (A : ι → Set T) (hA : Pairwise (Disjoint on A)) :
    timeToll γ (⋃ i, A i) m = ∑' i, timeToll γ (A i) m := by
  exact ENNReal.tsum_biUnion (f := fun t => m (γ t)) (fun i _ j _ hij => hA hij)

variable [MeasurableSpace Z]

theorem countable_image_incidence_bound (R : Set (Z × X)) (γ : T → X)
    (A : Set T) (ν : Measure Z) (m : X → ℝ≥0∞)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x) (hA : (γ '' A).Countable) :
    ν (timeIncidence R γ A) ≤ timeToll γ A m := by
  let : Countable (γ '' A) := hA.to_subtype
  have he : timeIncidence R γ A = ⋃ x : γ '' A, {z | (z, x.val) ∈ R} := by
    ext z
    constructor
    · rintro ⟨t, ht, hr⟩
      exact mem_iUnion.mpr ⟨⟨γ t, ⟨t, ht, rfl⟩⟩, hr⟩
    · intro hz
      obtain ⟨x, hx⟩ := mem_iUnion.mp hz
      obtain ⟨t, ht, he⟩ := x.property
      exact ⟨t, ht, he ▸ hx⟩
  let f : A → γ '' A := fun t => ⟨γ t, ⟨t, t.property, rfl⟩⟩
  have hf : Surjective f := by
    intro x
    obtain ⟨t, ht, he⟩ := x.property
    exact ⟨⟨t, ht⟩, Subtype.ext he⟩
  calc
    ν (timeIncidence R γ A) ≤ ∑' x : γ '' A, ν {z | (z, x.val) ∈ R} := by
      rw [he]
      exact measure_iUnion_le _
    _ ≤ ∑' x : γ '' A, m x := ENNReal.tsum_le_tsum fun x => hpoint x
    _ ≤ timeToll γ A m := ENNReal.tsum_le_tsum_comp_of_surjective hf (fun x => m x)

theorem countable_image_deleted_incidence_bound (R : Set (Z × X)) (P : Set X)
    (γ : T → X) (A : Set T) (ν : Measure Z) (m : X → ℝ≥0∞)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x) (hA : (γ '' A).Countable) :
    ν (timeIncidence {q | q ∈ R ∧ q.2 ∉ P} γ A) ≤ timeToll γ A (deletedWeight P m) := by
  apply countable_image_incidence_bound _ γ A ν _ _ hA
  intro x
  by_cases hx : x ∈ P
  · simp [deletedWeight, hx]
  · simpa [deletedWeight, hx] using hpoint x

theorem timeIncidence_bound_of_disjoint_cover {ι : Type*} [Countable ι]
    (R : Set (Z × X)) (γ : T → X) (A : Set T) (C : ι → Set T)
    (ν : Measure Z) (m : X → ℝ≥0∞) (hcover : A ⊆ ⋃ i, C i)
    (hsub : ∀ i, C i ⊆ A) (hdis : Pairwise (Disjoint on C))
    (hbound : ∀ i, ν (timeIncidence R γ (C i)) ≤ timeToll γ (C i) m) :
    ν (timeIncidence R γ A) ≤ timeToll γ A m := by
  have he : A = ⋃ i, C i := hcover.antisymm (iUnion_subset hsub)
  rw [he, timeIncidence_iUnion, timeToll_iUnion γ m C hdis]
  exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hbound)

end CircleDomainRigidity

end

end OAI
