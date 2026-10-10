import OAI.NumberTheory.TwoPoint.Bounds.ActualDesignations
import OAI.NumberTheory.TwoPoint.Bounds.ResidueTraceBound

namespace OAI

/-! Split an actual centered word into its singleton factors and lit designations. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {ι τ A : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]

def singletonSlots (label : τ → ι) : Finset τ :=
  univ.filter (fun t => label t ∈ singletonLabels label)

def nonsingletonSlots (label : τ → ι) : Finset τ :=
  univ.filter (fun t => label t ∈ nonsingletonLabels label)

lemma singleton_occurrence_exists (label : τ → ι) (i : singletonLabels label) :
    ∃ t, label t = i.val := by
  have hc := (mem_filter.mp i.property).2
  have hn : (labelOccurrences label i.val).Nonempty := card_pos.mp (by omega)
  obtain ⟨t, ht⟩ := hn
  exact ⟨t, (mem_filter.mp ht).2⟩

noncomputable def singletonRepresentative (label : τ → ι) (i : singletonLabels label) : τ :=
  Classical.choose (singleton_occurrence_exists label i)

lemma singletonRepresentative_label (label : τ → ι) (i : singletonLabels label) :
    label (singletonRepresentative label i) = i.val :=
  Classical.choose_spec (singleton_occurrence_exists label i)

lemma singleton_occurrence_unique (label : τ → ι) (i : singletonLabels label)
    (t : τ) (ht : label t = i.val) : t = singletonRepresentative label i := by
  obtain ⟨a, ha⟩ := card_eq_one.mp (mem_filter.mp i.property).2
  have htmem : t ∈ labelOccurrences label i.val := mem_filter.mpr ⟨mem_univ _, ht⟩
  have hrmem : singletonRepresentative label i ∈ labelOccurrences label i.val :=
    mem_filter.mpr ⟨mem_univ _, singletonRepresentative_label label i⟩
  rw [ha, mem_singleton] at htmem hrmem
  exact htmem.trans hrmem.symm

noncomputable def singletonTarget (label : τ → ι) (target : τ → A) (base : ι → A) : ι → A :=
  fun i => if hi : i ∈ singletonLabels label
    then target (singletonRepresentative label ⟨i, hi⟩) else base i

lemma singletonTarget_at (label : τ → ι) (target : τ → A) (base : ι → A)
    (t : τ) (ht : label t ∈ singletonLabels label) :
    singletonTarget label target base (label t) = target t := by
  simp only [singletonTarget, dite_eq_left ht]
  rw [← singleton_occurrence_unique label ⟨label t, ht⟩ t rfl]

lemma singletonSlots_product (label : τ → ι) (f : τ → ℝ) :
    (∏ t ∈ singletonSlots label, f t) =
      ∏ i : singletonLabels label, f (singletonRepresentative label i) := by
  apply prod_bij (fun t ht => (⟨label t, (mem_filter.mp ht).2⟩ : singletonLabels label))
  · intro t ht
    exact mem_univ _
  · intro t ht u hu he
    have htu : label t = label u := congrArg Subtype.val he
    exact (singleton_occurrence_unique label ⟨label t, (mem_filter.mp ht).2⟩ t rfl).trans
      (singleton_occurrence_unique label ⟨label t, (mem_filter.mp ht).2⟩ u htu.symm).symm
  · intro i _
    refine ⟨singletonRepresentative label i, ?_, ?_⟩
    · exact mem_filter.mpr ⟨mem_univ _, (singletonRepresentative_label label i).symm ▸ i.property⟩
    · exact Subtype.ext (singletonRepresentative_label label i)
  · intro t ht
    rw [← singleton_occurrence_unique label ⟨label t, (mem_filter.mp ht).2⟩ t rfl]

lemma centered_singleton_product [DecidableEq A]
    (label : τ → ι) (target : τ → A) (base x : ι → A) (θ : ι → ℝ) :
    (∏ t ∈ singletonSlots label,
      ((if x (label t) = target t then (1 : ℝ) else 0) - θ (label t))) =
      ∏ i ∈ singletonLabels label,
        ((if x i = singletonTarget label target base i then (1 : ℝ) else 0) - θ i) := by
  rw [singletonSlots_product]
  rw [← Finset.prod_coe_sort (s := singletonLabels label) (f := fun i : ι =>
    ((if x i = singletonTarget label target base i then (1 : ℝ) else 0) - θ i))]
  apply prod_congr rfl
  intro i _
  simp only [singletonRepresentative_label, singletonTarget, dite_eq_left i.property]

lemma centered_word_split [DecidableEq A]
    (label : τ → ι) (target : τ → A) (base x : ι → A) (θ : ι → ℝ) :
    (∏ t, ((if x (label t) = target t then (1 : ℝ) else 0) - θ (label t))) =
      (∏ t ∈ nonsingletonSlots label,
        ((if x (label t) = target t then (1 : ℝ) else 0) - θ (label t))) *
      ∏ i ∈ singletonLabels label,
        ((if x i = singletonTarget label target base i then (1 : ℝ) else 0) - θ i) := by
  rw [← centered_singleton_product label target base x θ]
  have he : singletonSlots label = univ.filter (fun t => t ∉ nonsingletonSlots label) := by
    ext t
    have hp : 0 < (labelOccurrences label (label t)).card :=
      card_pos.mpr ⟨t, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
    simp only [singletonSlots, nonsingletonSlots, singletonLabels, nonsingletonLabels,
      mem_filter, mem_univ, true_and]
    omega
  rw [he]
  have hcomp : univ.filter (fun t => t ∉ nonsingletonSlots label) =
      (nonsingletonSlots label)ᶜ := by ext t; simp
  rw [hcomp]
  exact (prod_mul_prod_compl (nonsingletonSlots label) (fun t : τ =>
    ((if x (label t) = target t then (1 : ℝ) else 0) - θ (label t)))).symm

/-- Every singleton remains centered while only nonsingleton occurrences
are expanded. This is an identity of signed word contributions. -/
lemma centered_word_designation_expansion [DecidableEq A]
    (label : τ → ι) (target : τ → A) (base x : ι → A) (θ : ι → ℝ)
    (R : ℝ) (G : (ι → A) → ℝ) :
    R * (∏ t, ((if x (label t) = target t then (1 : ℝ) else 0) - θ (label t))) * G x =
      ∑ U ∈ (nonsingletonSlots label).powerset,
        (R * ((-1 : ℝ) ^ U.card * ∏ t ∈ U, θ (label t))) *
          ((∏ t ∈ nonsingletonSlots label \ U,
            if x (label t) = target t then (1 : ℝ) else 0) *
            ((∏ i ∈ singletonLabels label,
              ((if x i = singletonTarget label target base i then (1 : ℝ) else 0) - θ i)) * G x)) := by
  rw [centered_word_split label target base x θ,
    centered_occurrence_expansion (nonsingletonSlots label) label target θ x]
  simp only [sum_mul, mul_sum]
  apply sum_congr rfl
  intro U _
  ring

/-- Averaging precedes the triangle inequality; no absolute value is
introduced while expanding the signed nonsingleton terms. -/
theorem centered_word_expectation [Fintype A] [DecidableEq A]
    (μ : FiniteLaw (ι → A)) (label : τ → ι) (target : τ → A)
    (base : ι → A) (θ : ι → ℝ) (R : ℝ) (G : (ι → A) → ℝ) :
    μ.average (fun x => R *
      (∏ t, ((if x (label t) = target t then (1 : ℝ) else 0) - θ (label t))) * G x) =
      ∑ U ∈ (nonsingletonSlots label).powerset, μ.average (fun x =>
        (R * ((-1 : ℝ) ^ U.card * ∏ t ∈ U, θ (label t))) *
          ((∏ t ∈ nonsingletonSlots label \ U,
            if x (label t) = target t then (1 : ℝ) else 0) *
            ((∏ i ∈ singletonLabels label,
              ((if x i = singletonTarget label target base i then (1 : ℝ) else 0) - θ i)) * G x))) := by
  simp_rw [centered_word_designation_expansion label target base _ θ R G]
  simp only [FiniteLaw.average, mul_sum]
  rw [sum_comm]

lemma singleton_disjoint_designated (label : τ → ι) (U : Finset τ) :
    Disjoint (singletonLabels label) ((nonsingletonSlots label \ U).image label) := by
  apply disjoint_left.mpr
  intro i hi hiL
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hiL
  exact singleton_not_nonsingleton label _ hi ((mem_filter.mp (mem_sdiff.mp ht).1).2)

end TwoPointCorrelations

end OAI
