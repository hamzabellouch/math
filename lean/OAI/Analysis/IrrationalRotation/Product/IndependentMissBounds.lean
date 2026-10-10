import Mathlib

namespace OAI

namespace Invariant233

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem measure_many_independent_events_le
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : ι → Set Ω) (hE : iIndepSet E μ) (s : Finset ι)
    {p : ℝ≥0∞} (hp : p ≤ 1) (hprob : ∀ i ∈ s, μ (E i) ≤ p) (q : ℝ) :
    μ {ω | ∃ t : Finset ι, t ⊆ s ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, ω ∈ E i} ≤
      (2 : ℝ≥0∞) ^ s.card * p ^ q := by
  classical
  let F := s.powerset.filter (fun t => q ≤ (t.card : ℝ))
  have hset : {ω | ∃ t : Finset ι, t ⊆ s ∧ q ≤ (t.card : ℝ) ∧
      ∀ i ∈ t, ω ∈ E i} = ⋃ t ∈ F, ⋂ i ∈ t, E i := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, F,
      Finset.mem_filter, Finset.mem_powerset]
    aesop
  have hFcard : F.card ≤ 2 ^ s.card := by
    calc
      F.card ≤ s.powerset.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 ^ s.card := Finset.card_powerset s
  rw [hset]
  calc
    μ (⋃ t ∈ F, ⋂ i ∈ t, E i) ≤ ∑ t ∈ F, μ (⋂ i ∈ t, E i) :=
      measure_biUnion_finset_le F _
    _ ≤ ∑ t ∈ F, p ^ q := by
      apply Finset.sum_le_sum
      intro t ht
      have ht' : t ⊆ s ∧ q ≤ (t.card : ℝ) := by
        simpa only [F, Finset.mem_filter, Finset.mem_powerset] using ht
      rw [hE.meas_biInter t]
      calc
        ∏ i ∈ t, μ (E i) ≤ ∏ _i ∈ t, p :=
          Finset.prod_le_prod (fun i hi => hprob i (ht'.1 hi))
        _ = p ^ t.card := by simp
        _ = p ^ (t.card : ℝ) := (ENNReal.rpow_natCast p t.card).symm
        _ ≤ p ^ q := ENNReal.rpow_le_rpow_of_exponent_ge hp ht'.2
    _ = (F.card : ℝ≥0∞) * p ^ q := by simp [nsmul_eq_mul]
    _ ≤ (2 : ℝ≥0∞) ^ s.card * p ^ q := by
      apply mul_le_mul_left
      exact_mod_cast hFcard

theorem measure_exists_many_independent_events_le
    {Ω ι κ : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : κ → ι → Set Ω) (s : Finset ι) (powers : Finset κ)
    (hE : ∀ k ∈ powers, iIndepSet (E k) μ)
    {p : ℝ≥0∞} (hp : p ≤ 1)
    (hprob : ∀ k ∈ powers, ∀ i ∈ s, μ (E k i) ≤ p) (q : ℝ) :
    μ {ω | ∃ k ∈ powers, ∃ t : Finset ι,
      t ⊆ s ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, ω ∈ E k i} ≤
      (powers.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ s.card * p ^ q) := by
  classical
  have hset : {ω | ∃ k ∈ powers, ∃ t : Finset ι,
      t ⊆ s ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, ω ∈ E k i} =
      ⋃ k ∈ powers, {ω | ∃ t : Finset ι,
        t ⊆ s ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, ω ∈ E k i} := by
    ext ω
    simp
  rw [hset]
  calc
    _ ≤ ∑ k ∈ powers, μ {ω | ∃ t : Finset ι,
        t ⊆ s ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, ω ∈ E k i} :=
      measure_biUnion_finset_le powers _
    _ ≤ ∑ _k ∈ powers, (2 : ℝ≥0∞) ^ s.card * p ^ q := by
      apply Finset.sum_le_sum
      intro k hk
      exact measure_many_independent_events_le μ (E k) (hE k hk) s hp
        (hprob k hk) q
    _ = _ := by simp [nsmul_eq_mul]

theorem exists_many_misses_of_few_successes {ι : Type*} (s : Finset ι)
    (good : ι → Prop) [DecidablePred good]
    (hgood : ((s.filter good).card : ℝ) < (s.card : ℝ) / 20) :
    ∃ t : Finset ι, t ⊆ s ∧ (19 / 20 : ℝ) * s.card < (t.card : ℝ) ∧
      ∀ i ∈ t, ¬ good i := by
  classical
  refine ⟨s.filter (fun i => ¬ good i), Finset.filter_subset _ _, ?_, ?_⟩
  · have hcard := Finset.card_filter_add_card_filter_not (s := s) good
    have hcardR : ((s.filter good).card : ℝ) +
        ((s.filter (fun i => ¬ good i)).card : ℝ) = s.card := by
      exact_mod_cast hcard
    linarith
  · intro i hi
    exact (Finset.mem_filter.mp hi).2

theorem measure_exists_few_successes_le
    {Ω ι κ : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (good : κ → ι → Ω → Prop) [∀ k i ω, Decidable (good k i ω)]
    (s : Finset ι) (powers : Finset κ)
    (hE : ∀ k ∈ powers, iIndepSet (fun i => {ω | ¬ good k i ω}) μ)
    {p : ℝ≥0∞} (hp : p ≤ 1)
    (hprob : ∀ k ∈ powers, ∀ i ∈ s, μ {ω | ¬ good k i ω} ≤ p) :
    μ {ω | ∃ k ∈ powers,
      ((s.filter (fun i => good k i ω)).card : ℝ) < (s.card : ℝ) / 20} ≤
      (powers.card : ℝ≥0∞) *
        ((2 : ℝ≥0∞) ^ s.card * p ^ ((19 / 20 : ℝ) * s.card)) := by
  calc
    _ ≤ μ {ω | ∃ k ∈ powers, ∃ t : Finset ι,
        t ⊆ s ∧ (19 / 20 : ℝ) * s.card ≤ (t.card : ℝ) ∧
          ∀ i ∈ t, ω ∈ {ω | ¬ good k i ω}} := by
      apply measure_mono
      intro ω hω
      obtain ⟨k, hk, hgood⟩ := hω
      obtain ⟨t, hts, htcard, htbad⟩ :=
        exists_many_misses_of_few_successes s (fun i => good k i ω) hgood
      exact ⟨k, hk, t, hts, htcard.le, htbad⟩
    _ ≤ _ := measure_exists_many_independent_events_le μ
      (fun k i => {ω | ¬ good k i ω}) s powers hE hp hprob _

end Invariant233

end OAI
