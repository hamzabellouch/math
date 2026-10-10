import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

namespace OAI

open scoped BigOperators ENNReal
open MeasureTheory

namespace Balanced.MarkedExposure

variable {Ω ι : Type*}

noncomputable def atLeast (s : Finset ι) (E : ι → Set Ω) (r : ℕ) : Set Ω :=
  by
    classical
    exact {ω | r ≤ (s.filter fun i => ω ∈ E i).card}

theorem atLeast_subset_union (s : Finset ι) (E : ι → Set Ω) (r : ℕ) :
    atLeast s E r ⊆ ⋃ t ∈ s.powersetCard r, ⋂ i ∈ t, E i := by
  classical
  intro ω hω
  change r ≤ (s.filter fun i => ω ∈ E i).card at hω
  obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq hω
  refine Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_powersetCard.mpr ⟨ht.trans (Finset.filter_subset _ _), hcard⟩
  · simp only [Set.mem_iInter]
    intro i hi
    exact (Finset.mem_filter.mp (ht hi)).2

variable [MeasurableSpace Ω]

theorem tail_le_choose_mul (μ : Measure Ω) (s : Finset ι) (E : ι → Set Ω)
    (r : ℕ) (p : ℝ≥0∞)
    (h : ∀ t ∈ s.powersetCard r, μ (⋂ i ∈ t, E i) ≤ p ^ r) :
    μ (atLeast s E r) ≤ (s.card.choose r : ℝ≥0∞) * p ^ r := by
  classical
  calc
    μ (atLeast s E r) ≤ μ (⋃ t ∈ s.powersetCard r, ⋂ i ∈ t, E i) :=
      measure_mono (atLeast_subset_union s E r)
    _ ≤ ∑ t ∈ s.powersetCard r, μ (⋂ i ∈ t, E i) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _t ∈ s.powersetCard r, p ^ r := Finset.sum_le_sum h
    _ = (s.card.choose r : ℝ≥0∞) * p ^ r := by simp

theorem tail_le_two_pow_mul (μ : Measure Ω) (s : Finset ι) (E : ι → Set Ω)
    (r : ℕ) (p : ℝ≥0∞)
    (h : ∀ t ∈ s.powersetCard r, μ (⋂ i ∈ t, E i) ≤ p ^ r) :
    μ (atLeast s E r) ≤ (2 : ℝ≥0∞) ^ s.card * p ^ r := by
  refine (tail_le_choose_mul μ s E r p h).trans ?_
  apply mul_le_mul_left
  exact_mod_cast Nat.choose_le_two_pow s.card r

theorem intersection_le_pow_of_step (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : ℕ → Set Ω) (N : ℕ) (p : ℝ≥0∞)
    (hstep : ∀ j < N, ∀ t : Finset ℕ, t ⊆ Finset.range j →
      μ (E j ∩ (⋂ i ∈ t, E i)) ≤ p * μ (⋂ i ∈ t, E i))
    (t : Finset ℕ) (ht : t ⊆ Finset.range N) :
    μ (⋂ i ∈ t, E i) ≤ p ^ t.card := by
  induction t using Finset.induction_on_max with
  | empty => simp
  | insert j t hj ih =>
    have hjN : j < N := Finset.mem_range.mp (ht (Finset.mem_insert_self j t))
    have htt : t ⊆ Finset.range N := fun i hi => ht (Finset.mem_insert_of_mem hi)
    have hjt : j ∉ t := fun h => (hj j h).false
    have htr : t ⊆ Finset.range j := fun i hi => Finset.mem_range.mpr (hj i hi)
    calc
      μ (⋂ i ∈ insert j t, E i) = μ (E j ∩ (⋂ i ∈ t, E i)) := by
        congr 1
        ext ω
        simp
      _ ≤ p * μ (⋂ i ∈ t, E i) := hstep j hjN t htr
      _ ≤ p * p ^ t.card := by gcongr; exact ih htt
      _ = p ^ (insert j t).card := by rw [Finset.card_insert_of_notMem hjt, pow_succ']

theorem tail_le_two_pow_mul_of_step (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : ℕ → Set Ω) (N r : ℕ) (p : ℝ≥0∞)
    (hstep : ∀ j < N, ∀ t : Finset ℕ, t ⊆ Finset.range j →
      μ (E j ∩ (⋂ i ∈ t, E i)) ≤ p * μ (⋂ i ∈ t, E i)) :
    μ (atLeast (Finset.range N) E r) ≤ (2 : ℝ≥0∞) ^ N * p ^ r := by
  simpa using tail_le_two_pow_mul μ (Finset.range N) E r p (by
    intro t ht
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp ht
    simpa [hcard] using intersection_le_pow_of_step μ E N p hstep t hsub)

noncomputable def tailMass (s : Finset ι) (w X : ι → ℝ) (a : ℝ) : ℝ := by
  classical
  exact ∑ i ∈ s, if a ≤ X i then w i else 0

theorem tailMass_lower_bound (s : Finset ι) (w X : ι → ℝ) (m n ξ : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hn : 0 < n) (hξ : 0 ≤ ξ)
    (hbound : ∀ i ∈ s, X i ≤ m + n)
    (hexpect : m + ξ ≤ ∑ i ∈ s, w i * X i) :
    ξ / (2 * n) ≤ tailMass s w X (m + ξ / 2) := by
  classical
  have hpoint (i : ι) (hi : i ∈ s) :
      w i * X i ≤ w i * (m + ξ / 2) +
        n * (if m + ξ / 2 ≤ X i then w i else 0) := by
    split_ifs with h
    · nlinarith [mul_nonneg (hw i hi) hξ,
        mul_le_mul_of_nonneg_left (hbound i hi) (hw i hi)]
    · have hx : X i < m + ξ / 2 := lt_of_not_ge h
      nlinarith [mul_le_mul_of_nonneg_left (le_of_lt hx) (hw i hi)]
  have hsumBound := Finset.sum_le_sum hpoint
  have hright : (∑ i ∈ s, (w i * (m + ξ / 2) +
      n * (if m + ξ / 2 ≤ X i then w i else 0))) =
      m + ξ / 2 + n * tailMass s w X (m + ξ / 2) := by
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      hsum, one_mul, tailMass]
  rw [hright] at hsumBound
  apply (div_le_iff₀ (by positivity : 0 < 2 * n)).mpr
  nlinarith

theorem measureReal_tail_lower_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (m n ξ : ℝ) (hX : Integrable X μ)
    (hE : MeasurableSet {ω | m + ξ / 2 ≤ X ω})
    (hn : 0 < n) (hξ : 0 ≤ ξ)
    (hbound : ∀ᵐ ω ∂μ, X ω ≤ m + n)
    (hexpect : m + ξ ≤ ∫ ω, X ω ∂μ) :
    ξ / (2 * n) ≤ μ.real {ω | m + ξ / 2 ≤ X ω} := by
  classical
  let E : Set Ω := {ω | m + ξ / 2 ≤ X ω}
  let Y : Ω → ℝ := E.indicator (fun _ => 1)
  have hY : Integrable Y μ := (integrable_const (1 : ℝ)).indicator hE
  have hpoint : ∀ᵐ ω ∂μ, X ω ≤ m + ξ / 2 + n * Y ω := by
    filter_upwards [hbound] with ω hω
    by_cases h : ω ∈ E
    · have hYω : Y ω = 1 := Set.indicator_of_mem h _
      rw [hYω]
      linarith
    · have hYω : Y ω = 0 := Set.indicator_of_notMem h _
      have hω' : X ω < m + ξ / 2 := lt_of_not_ge h
      rw [hYω]
      linarith
  have hle := integral_mono_ae hX ((integrable_const (m + ξ / 2)).add
    (hY.const_mul n)) hpoint
  have hintY : (∫ ω, Y ω ∂μ) = μ.real E := integral_indicator_one hE
  simp only [Pi.add_apply] at hle
  rw [integral_add (integrable_const _) (hY.const_mul n), integral_const,
    integral_const_mul, hintY] at hle
  simp only [probReal_univ, smul_eq_mul, one_mul] at hle
  apply (div_le_iff₀ (by positivity : 0 < 2 * n)).mpr
  change ξ ≤ μ.real E * (2 * n)
  nlinarith

theorem normalized_deviation_iff (x N q ε : ℝ) (hq : 0 < q) :
    ε < |x / q - N / q ^ 2| ↔ ε * q < |x - N / q| := by
  have heq : x / q - N / q ^ 2 = (x - N / q) / q := by
    field_simp
  rw [heq, abs_div, abs_of_pos hq, lt_div_iff₀ hq]

theorem card_large_deviations_le (s : Finset ι) (x : ι → ℝ)
    (mean q ε : ℝ) (hq : 0 < q) (hε : 0 < ε)
    (hvariance : ∑ i ∈ s, (x i - mean) ^ 2 ≤ q ^ 3 / 4) :
    ((s.filter fun i => ε * q < |x i - mean|).card : ℝ) ≤ q / (4 * ε ^ 2) := by
  classical
  let b := s.filter fun i => ε * q < |x i - mean|
  have hlower : (b.card : ℝ) * (ε * q) ^ 2 ≤ q ^ 3 / 4 := by
    calc
      (b.card : ℝ) * (ε * q) ^ 2 = ∑ _i ∈ b, (ε * q) ^ 2 := by simp
      _ ≤ ∑ i ∈ b, (x i - mean) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := (Finset.mem_filter.mp hi).2
        have hs := (sq_le_sq₀ (by positivity : 0 ≤ ε * q) (abs_nonneg (x i - mean))).2 hi'.le
        simpa only [sq_abs] using hs
      _ ≤ ∑ i ∈ s, (x i - mean) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => sq_nonneg _)
      _ ≤ q ^ 3 / 4 := hvariance
  change (b.card : ℝ) ≤ q / (4 * ε ^ 2)
  apply (le_div_iff₀ (by positivity : 0 < 4 * ε ^ 2)).mpr
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < q ^ 2)).mp
  nlinarith [hlower]

theorem mass_large_deviations_le (s : Finset ι) (x w : ι → ℝ)
    (mean q ε C : ℝ) (hq : 0 < q) (hε : 0 < ε) (hC : 0 ≤ C)
    (hvariance : ∑ i ∈ s, (x i - mean) ^ 2 ≤ q ^ 3 / 4)
    (hweight : ∀ i ∈ s, w i ≤ C / q ^ 2) :
    (∑ i ∈ s.filter (fun i => ε * q < |x i - mean|), w i) ≤ C / (4 * ε ^ 2 * q) := by
  classical
  let b := s.filter fun i => ε * q < |x i - mean|
  have hcard := card_large_deviations_le s x mean q ε hq hε hvariance
  change (b.card : ℝ) ≤ q / (4 * ε ^ 2) at hcard
  calc
    (∑ i ∈ b, w i) ≤ ∑ _i ∈ b, C / q ^ 2 := by
      exact Finset.sum_le_sum (fun i hi => hweight i (Finset.mem_filter.mp hi).1)
    _ = (b.card : ℝ) * (C / q ^ 2) := by simp
    _ ≤ (q / (4 * ε ^ 2)) * (C / q ^ 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = C / (4 * ε ^ 2 * q) := by field_simp

end Balanced.MarkedExposure

end OAI
