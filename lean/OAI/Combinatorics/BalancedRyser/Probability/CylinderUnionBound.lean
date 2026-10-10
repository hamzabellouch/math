import Mathlib.Data.Finset.Powerset
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace BalancedRyser

attribute [local instance] Classical.propDecidable

theorem at_least_subset_cylinder_union
    {Ω ι : Type*} [DecidableEq ι]
    (s : Finset ι) (E : ι → Set Ω) (A : Set Ω) (m : ℕ) :
    {ω | ω ∈ A ∧ m ≤ (s.filter (fun i => ω ∈ E i)).card} ⊆
      ⋃ t ∈ s.powersetCard m, A ∩ ⋂ i ∈ t, E i := by
  classical
  intro ω hω
  obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq hω.2
  have hts : t ⊆ s := ht.trans (Finset.filter_subset _ _)
  refine Set.mem_iUnion.2 ⟨t, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
  · exact Finset.mem_powersetCard.2 ⟨hts, hcard⟩
  · refine ⟨hω.1, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    exact (Finset.mem_filter.1 (ht hi)).2

theorem measure_at_least_of_cylinder_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (s : Finset ι) (E : ι → Set Ω) (A : Set Ω)
    (m : ℕ) (δ : ℝ≥0∞)
    (hcyl : ∀ t ∈ s.powersetCard m, μ (A ∩ ⋂ i ∈ t, E i) ≤ δ ^ m) :
    μ {ω | ω ∈ A ∧ m ≤ (s.filter (fun i => ω ∈ E i)).card} ≤
      (s.card.choose m : ℝ≥0∞) * δ ^ m := by
  classical
  have hsub := at_least_subset_cylinder_union s E A m
  calc
    μ {ω | ω ∈ A ∧ m ≤ (s.filter (fun i => ω ∈ E i)).card}
        ≤ μ (⋃ t ∈ s.powersetCard m, A ∩ ⋂ i ∈ t, E i) := measure_mono hsub
    _ ≤ ∑ t ∈ s.powersetCard m, μ (A ∩ ⋂ i ∈ t, E i) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _t ∈ s.powersetCard m, δ ^ m := Finset.sum_le_sum hcyl
    _ = (s.card.choose m : ℝ≥0∞) * δ ^ m := by
      simp [Finset.card_powersetCard, nsmul_eq_mul]

theorem measureReal_at_least_of_cylinder_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : Finset ι) (E : ι → Set Ω) (A : Set Ω)
    (m : ℕ) (δ : ℝ)
    (hcyl : ∀ t ∈ s.powersetCard m, μ.real (A ∩ ⋂ i ∈ t, E i) ≤ δ ^ m) :
    μ.real {ω | ω ∈ A ∧ m ≤ (s.filter (fun i => ω ∈ E i)).card} ≤
      (s.card.choose m : ℝ) * δ ^ m := by
  classical
  have hsub := at_least_subset_cylinder_union s E A m
  calc
    μ.real {ω | ω ∈ A ∧ m ≤ (s.filter (fun i => ω ∈ E i)).card}
        ≤ μ.real (⋃ t ∈ s.powersetCard m, A ∩ ⋂ i ∈ t, E i) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ t ∈ s.powersetCard m, μ.real (A ∩ ⋂ i ∈ t, E i) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _t ∈ s.powersetCard m, δ ^ m := Finset.sum_le_sum hcyl
    _ = (s.card.choose m : ℝ) * δ ^ m := by
      simp [Finset.card_powersetCard, nsmul_eq_mul]

theorem measureReal_exists_at_least_of_cylinder_bound
    {Ω ι π : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : Finset π) (s : Finset ι) (E : π → ι → Set Ω) (A : Set Ω)
    (m : ℕ) (δ : ℝ)
    (hcyl : ∀ p ∈ P, ∀ t ∈ s.powersetCard m,
      μ.real (A ∩ ⋂ i ∈ t, E p i) ≤ δ ^ m) :
    μ.real (⋃ p ∈ P,
      {ω | ω ∈ A ∧ m ≤ (s.filter (fun i => ω ∈ E p i)).card}) ≤
      (P.card : ℝ) * ((s.card.choose m : ℝ) * δ ^ m) := by
  classical
  calc
    μ.real (⋃ p ∈ P,
        {ω | ω ∈ A ∧ m ≤ (s.filter (fun i => ω ∈ E p i)).card})
        ≤ ∑ p ∈ P, μ.real
          {ω | ω ∈ A ∧ m ≤ (s.filter (fun i => ω ∈ E p i)).card} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ P, (s.card.choose m : ℝ) * δ ^ m := by
      apply Finset.sum_le_sum
      intro p hp
      exact measureReal_at_least_of_cylinder_bound μ s (E p) A m δ (hcyl p hp)
    _ = (P.card : ℝ) * ((s.card.choose m : ℝ) * δ ^ m) := by
      simp [nsmul_eq_mul]

theorem subsingleton_predicate_cylinder_eq_or_empty
    {Ω ι : Type*} {Q : ι → Type*} [DecidableEq ι]
    (V : Ω → ∀ i, Q i) (t : Finset ι) (P : ∀ i, Q i → Prop) (A : Set Ω)
    (hunique : ∀ i ∈ t, Set.Subsingleton {v : Q i | P i v}) :
    (A ∩ ⋂ i ∈ t, {ω | P i (V ω i)}) = ∅ ∨
      ∃ v : ∀ i, Q i,
        (A ∩ ⋂ i ∈ t, {ω | P i (V ω i)}) =
          A ∩ ⋂ i ∈ t, {ω | V ω i = v i} := by
  classical
  by_cases hne : (A ∩ ⋂ i ∈ t, {ω | P i (V ω i)}).Nonempty
  · obtain ⟨ω₀, hω₀⟩ := hne
    have hP₀ : ∀ i ∈ t, P i (V ω₀ i) := by simpa using hω₀.2
    refine Or.inr ⟨V ω₀, ?_⟩
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hA, hP⟩
      exact ⟨hA, fun i hi => hunique i hi (hP i hi) (hP₀ i hi)⟩
    · rintro ⟨hA, heq⟩
      exact ⟨hA, fun i hi => (heq i hi) ▸ hP₀ i hi⟩
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)

theorem measure_subsingleton_predicate_cylinder
    {Ω ι : Type*} [MeasurableSpace Ω] {Q : ι → Type*} [DecidableEq ι]
    (μ : Measure Ω) (V : Ω → ∀ i, Q i)
    (t : Finset ι) (P : ∀ i, Q i → Prop) (A : Set Ω) (δ : ℝ≥0∞)
    (hunique : ∀ i ∈ t, Set.Subsingleton {v : Q i | P i v})
    (hcyl : ∀ v : ∀ i, Q i,
      μ (A ∩ ⋂ i ∈ t, {ω | V ω i = v i}) ≤ δ ^ t.card) :
    μ (A ∩ ⋂ i ∈ t, {ω | P i (V ω i)}) ≤ δ ^ t.card := by
  obtain h | ⟨v, h⟩ := subsingleton_predicate_cylinder_eq_or_empty V t P A hunique
  · simp [h]
  · rw [h]
    exact hcyl v

theorem measureReal_subsingleton_predicate_cylinder
    {Ω ι : Type*} [MeasurableSpace Ω] {Q : ι → Type*} [DecidableEq ι]
    (μ : Measure Ω) (V : Ω → ∀ i, Q i)
    (t : Finset ι) (P : ∀ i, Q i → Prop) (A : Set Ω) (δ : ℝ) (hδ : 0 ≤ δ)
    (hunique : ∀ i ∈ t, Set.Subsingleton {v : Q i | P i v})
    (hcyl : ∀ v : ∀ i, Q i,
      μ.real (A ∩ ⋂ i ∈ t, {ω | V ω i = v i}) ≤ δ ^ t.card) :
    μ.real (A ∩ ⋂ i ∈ t, {ω | P i (V ω i)}) ≤ δ ^ t.card := by
  obtain h | ⟨v, h⟩ := subsingleton_predicate_cylinder_eq_or_empty V t P A hunique
  · simp only [h, measureReal_empty]
    exact pow_nonneg hδ _
  · rw [h]
    exact hcyl v

theorem measureReal_at_least_subsingleton_predicates
    {Ω ι : Type*} [MeasurableSpace Ω] {Q : ι → Type*} [DecidableEq ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (V : Ω → ∀ i, Q i)
    (s : Finset ι) (P : ∀ i, Q i → Prop) (A : Set Ω)
    (m : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hunique : ∀ i ∈ s, Set.Subsingleton {v : Q i | P i v})
    (hcyl : ∀ t ⊆ s, ∀ v : ∀ i, Q i,
      μ.real (A ∩ ⋂ i ∈ t, {ω | V ω i = v i}) ≤ δ ^ t.card) :
    μ.real {ω | ω ∈ A ∧ m ≤ (s.filter (fun i => P i (V ω i))).card} ≤
      (s.card.choose m : ℝ) * δ ^ m := by
  classical
  apply measureReal_at_least_of_cylinder_bound μ s (fun i => {ω | P i (V ω i)}) A m δ
  intro t ht
  obtain ⟨hts, hcard⟩ := Finset.mem_powersetCard.1 ht
  have hbound := measureReal_subsingleton_predicate_cylinder μ V t P A δ hδ
    (fun i hi => hunique i (hts hi)) (hcyl t hts)
  simpa only [hcard] using hbound

end BalancedRyser

end OAI
