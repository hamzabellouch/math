import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- A finite Markov inequality with a union over frequencies. No independence
between the frequencies, or between the points, is required. -/
theorem card_exists_large_score_mul_le {α β : Type*}
    (U : Finset α) (L : Finset β) (g : α → β → ℝ) (a : ℝ)
    (hg : ∀ u ∈ U, ∀ l ∈ L, 0 ≤ g u l) :
    ((U.filter (fun u => ∃ l ∈ L, a < g u l)).card : ℝ) * a ≤
      ∑ l ∈ L, ∑ u ∈ U, g u l := by
  classical
  let bad := U.filter (fun u => ∃ l ∈ L, a < g u l)
  calc
    (bad.card : ℝ) * a = ∑ _u ∈ bad, a := by simp
    _ ≤ ∑ u ∈ bad, ∑ l ∈ L, g u l := by
      apply Finset.sum_le_sum
      intro u hu
      obtain ⟨huU, l, hl, hlarge⟩ := Finset.mem_filter.mp hu
      exact hlarge.le.trans (Finset.single_le_sum (hg u huU) hl)
    _ ≤ ∑ u ∈ U, ∑ l ∈ L, g u l := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro u hu _
      exact Finset.sum_nonneg (hg u hu)
    _ = ∑ l ∈ L, ∑ u ∈ U, g u l := Finset.sum_comm

/-- Squared complex Fourier scores are a common instance of the preceding
finite Markov/union estimate. -/
theorem card_exists_large_norm_sq_mul_le {α β : Type*}
    (U : Finset α) (L : Finset β) (f : α → β → ℂ) (a : ℝ) (ha : 0 ≤ a) :
    ((U.filter (fun u => ∃ l ∈ L, a < ‖f u l‖)).card : ℝ) * a ^ 2 ≤
      ∑ l ∈ L, ∑ u ∈ U, ‖f u l‖ ^ 2 := by
  classical
  have hfilter : U.filter (fun u => ∃ l ∈ L, a < ‖f u l‖) =
      U.filter (fun u => ∃ l ∈ L, a ^ 2 < ‖f u l‖ ^ 2) := by
    apply Finset.filter_congr
    intro u _
    apply exists_congr
    intro l
    exact and_congr_right (fun _ => by
      constructor
      · intro h
        nlinarith [norm_nonneg (f u l)]
      · intro h
        nlinarith [norm_nonneg (f u l)])
  rw [hfilter]
  apply card_exists_large_score_mul_le
  intros
  positivity

/-- A finite probabilistic-method selection principle. A normalized total
expectation below one gives one sample satisfying all the thresholds. -/
theorem exists_simultaneous_below_thresholds {Ω J : Type*}
    (samples : Finset Ω) (tests : Finset J)
    (score : Ω → J → ℝ) (threshold : J → ℝ)
    (hnonneg : ∀ ω ∈ samples, ∀ j ∈ tests, 0 ≤ score ω j)
    (hpos : ∀ j ∈ tests, 0 < threshold j)
    (hbudget : (∑ j ∈ tests, (∑ ω ∈ samples, score ω j) / threshold j) <
      (samples.card : ℝ)) :
    ∃ ω ∈ samples, ∀ j ∈ tests, score ω j < threshold j := by
  have htotal : (∑ ω ∈ samples, ∑ j ∈ tests, score ω j / threshold j) <
      ∑ _ω ∈ samples, (1 : ℝ) := by
    calc
      (∑ ω ∈ samples, ∑ j ∈ tests, score ω j / threshold j) =
          ∑ j ∈ tests, (∑ ω ∈ samples, score ω j) / threshold j := by
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_div]
      _ < (samples.card : ℝ) := hbudget
      _ = ∑ _ω ∈ samples, (1 : ℝ) := by simp
  obtain ⟨ω, hω, hsmall⟩ := Finset.exists_lt_of_sum_lt htotal
  refine ⟨ω, hω, ?_⟩
  intro j hj
  have hsingle : score ω j / threshold j ≤
      ∑ i ∈ tests, score ω i / threshold i := by
    apply Finset.single_le_sum _ hj
    intro i hi
    exact div_nonneg (hnonneg ω hω i hi) (hpos i hi).le
  have hratio : score ω j / threshold j < 1 := hsingle.trans_lt hsmall
  exact (div_lt_iff₀ (hpos j hj)).mp hratio |>.trans_eq (one_mul _)

/-- Convenient per-test mean bounds for simultaneous selection. -/
theorem exists_simultaneous_of_mean_bounds {Ω J : Type*}
    (samples : Finset Ω) (tests : Finset J) (hsamples : samples.Nonempty)
    (score : Ω → J → ℝ) (threshold ε : J → ℝ)
    (hnonneg : ∀ ω ∈ samples, ∀ j ∈ tests, 0 ≤ score ω j)
    (hpos : ∀ j ∈ tests, 0 < threshold j)
    (hmean : ∀ j ∈ tests,
      (∑ ω ∈ samples, score ω j) ≤ (samples.card : ℝ) * ε j * threshold j)
    (hε : (∑ j ∈ tests, ε j) < 1) :
    ∃ ω ∈ samples, ∀ j ∈ tests, score ω j < threshold j := by
  apply exists_simultaneous_below_thresholds samples tests score threshold hnonneg hpos
  have hcard : (0 : ℝ) < samples.card := by exact_mod_cast hsamples.card_pos
  calc
    (∑ j ∈ tests, (∑ ω ∈ samples, score ω j) / threshold j) ≤
        ∑ j ∈ tests, (samples.card : ℝ) * ε j := by
      apply Finset.sum_le_sum
      intro j hj
      exact (div_le_iff₀ (hpos j hj)).2 (hmean j hj)
    _ = (samples.card : ℝ) * ∑ j ∈ tests, ε j := by rw [Finset.mul_sum]
    _ < (samples.card : ℝ) * 1 := mul_lt_mul_of_pos_left hε hcard
    _ = (samples.card : ℝ) := mul_one _

/-- The uniform second-moment version of the frequency-union bound. -/
theorem card_exists_large_norm_le_of_moments {α β : Type*}
    (U : Finset α) (L : Finset β) (f : α → β → ℂ) (a E : ℝ)
    (ha : 0 < a) (hE : ∀ l ∈ L, (∑ u ∈ U, ‖f u l‖ ^ 2) ≤ E) :
    ((U.filter (fun u => ∃ l ∈ L, a < ‖f u l‖)).card : ℝ) ≤
      (L.card : ℝ) * E / a ^ 2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos ha)).2
  calc
    ((U.filter (fun u => ∃ l ∈ L, a < ‖f u l‖)).card : ℝ) * a ^ 2 ≤
        ∑ l ∈ L, ∑ u ∈ U, ‖f u l‖ ^ 2 :=
      card_exists_large_norm_sq_mul_le U L f a ha.le
    _ ≤ ∑ _l ∈ L, E := Finset.sum_le_sum hE
    _ = (L.card : ℝ) * E := by simp

/-- A finite product-space union bound. Each test fails only if every
coordinate belongs to its corresponding bad set. Different tests need not
be independent. Allowed coordinate sets may be different, so one coordinate
can simultaneously enforce a separate collection of middle-level tests. -/
theorem exists_product_sample_avoiding {ι Ω J : Type*} [Fintype ι]
    (allowed : ι → Finset Ω) (tests : Finset J) (bad : J → ι → Finset Ω)
    (hbudget : (∑ j ∈ tests, ∏ i, (bad j i).card) < ∏ i, (allowed i).card) :
    ∃ sample : ι → Ω, (∀ i, sample i ∈ allowed i) ∧
      ∀ j ∈ tests, ∃ i, sample i ∉ bad j i := by
  classical
  let allBad : Finset (ι → Ω) := tests.biUnion (fun j => Fintype.piFinset (bad j))
  have hcard : allBad.card < (Fintype.piFinset allowed).card := by
    calc
      allBad.card ≤ ∑ j ∈ tests, (Fintype.piFinset (bad j)).card := Finset.card_biUnion_le
      _ = ∑ j ∈ tests, ∏ i, (bad j i).card := by simp only [Fintype.card_piFinset]
      _ < ∏ i, (allowed i).card := hbudget
      _ = (Fintype.piFinset allowed).card := (Fintype.card_piFinset allowed).symm
  obtain ⟨sample, hsample, havoid⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨sample, Fintype.mem_piFinset.mp hsample, ?_⟩
  intro j hj
  by_contra h
  push Not at h
  exact havoid (Finset.mem_biUnion.mpr ⟨j, hj, Fintype.mem_piFinset.mpr h⟩)

/-- Independent repetitions amplify a per-test failure cardinality to its
`R`-th power. This is the terminal-block selection step in finite form. -/
theorem exists_repeated_samples_avoiding {Ω J : Type*}
    (samples : Finset Ω) (tests : Finset J) (bad : J → Finset Ω) (R : ℕ)
    (hbudget : (∑ j ∈ tests, (bad j).card ^ R) < samples.card ^ R) :
    ∃ sample : Fin R → Ω, (∀ i, sample i ∈ samples) ∧
      ∀ j ∈ tests, ∃ i, sample i ∉ bad j := by
  apply exists_product_sample_avoiding (fun _ : Fin R => samples) tests
    (fun j _ => bad j)
  simpa using hbudget

end Problem337

end

end OAI
