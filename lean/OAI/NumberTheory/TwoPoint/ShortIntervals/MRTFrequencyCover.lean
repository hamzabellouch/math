import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFrequencyPartition

namespace OAI

/-! Refinement of a later frequency class by its actual preceding-bin
large-value witnesses. The witnesses may overlap; the finite sum charges
each preceding bin explicitly. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_nonnegative_integral_cover {ι : Type*} (I : Finset ι)
    (E : ι → Set ℝ) (hE : ∀ i ∈ I, MeasurableSet (E i)) {S : Set ℝ}
    (hS : MeasurableSet S) (f : ℝ → ℝ) (hf : IntegrableOn f S)
    (hf0 : ∀ t ∈ S, 0 ≤ f t) (hcover : ∀ t ∈ S, ∃ i ∈ I, t ∈ E i) :
    (∫ t in S, f t) ≤ ∑ i ∈ I, ∫ t in S ∩ E i, f t := by
  have hi (i : ι) (hmem : i ∈ I) : IntegrableOn ((E i).indicator f) S :=
    hf.indicator (hE i hmem)
  calc
    _ ≤ ∫ t in S, ∑ i ∈ I, (E i).indicator f t := by
      apply setIntegral_mono_on hf (integrable_finsetSum I hi) hS
      intro t ht
      obtain ⟨i, hiI, hit⟩ := hcover t ht
      calc
        f t = (E i).indicator f t := (Set.indicator_of_mem hit f).symm
        _ ≤ ∑ i ∈ I, (E i).indicator f t := by
          apply single_le_sum _ hiI
          intro k _
          by_cases hk : t ∈ E k
          · rw [Set.indicator_of_mem hk f]
            exact hf0 t ht
          · rw [Set.indicator_of_notMem hk f]
    _ = ∑ i ∈ I, ∫ t in S, (E i).indicator f t := integral_finsetSum I hi
    _ = _ := by
      apply sum_congr rfl
      intro i hiI
      exact setIntegral_indicator (hE i hiI)

theorem mrt_later_band_integral_cover {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ)
    (hQ : ∀ j k, Continuous (Q j k)) {j : ℕ} (hj : 0 < j)
    {S : Set ℝ} (hS : MeasurableSet S) (f : ℝ → ℝ) (hf : IntegrableOn f S)
    (hf0 : ∀ t ∈ S, 0 ≤ f t) :
    (∫ t in S ∩ mrtFirstSmallBand K Q A j, f t) ≤
      ∑ k ∈ K (j - 1),
        ∫ t in (S ∩ mrtFirstSmallBand K Q A j) ∩
          {t | A (j - 1) k < ‖Q (j - 1) k t‖}, f t := by
  apply mrt_nonnegative_integral_cover (K (j - 1))
    (fun k => {t | A (j - 1) k < ‖Q (j - 1) k t‖})
    (fun k _ => (isOpen_lt continuous_const (hQ (j - 1) k).norm).measurableSet)
    (hS.inter (mrt_first_small_band_measurable K Q A hQ j)) f
    (hf.mono_set Set.inter_subset_left) (fun t ht => hf0 t ht.1)
  intro t ht
  exact mrt_later_band_large_witness K Q A hj ht.2

end TwoPointCorrelations

end OAI
