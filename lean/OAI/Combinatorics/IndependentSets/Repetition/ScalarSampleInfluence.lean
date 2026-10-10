import Mathlib
import OAI.Combinatorics.IndependentSets.Repetition.ScalarCell

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set
open scoped BigOperators Classical NNReal ENNReal

noncomputable def scalarSampleInfluence {m : ℕ} (f : ℝ → ℝ) (i : Fin m) : ℝ :=
  mean (fun q : Cube m => ∫ y in (0:ℝ)..1,
    |(f (scalarCell q y) - f (scalarCell (flip i q) y))/2|)

lemma scalarSampleInfluence_succ {m : ℕ} (f : ℝ → ℝ) (i : Fin m) :
    scalarSampleInfluence (m:=m+1) f i.succ =
      (scalarSampleInfluence (m:=m) (f ∘ halfInput false) i +
       scalarSampleInfluence (m:=m) (f ∘ halfInput true) i)/2 := by
  rw [scalarSampleInfluence, mean_succ]
  rfl

lemma scalarCell_difference {m : ℕ} {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (q r : Cube m) {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) :
    |f (scalarCell q y) - f (scalarCell r y)| ≤ variation f := by
  have hq := scalarCell_mem q hy
  have hr := scalarCell_mem r hy
  rcases le_total (scalarCell q y) (scalarCell r y) with h | h
  · rw [abs_sub_comm]
    exact CubeGradient.slice_difference_le_variation hf hq.1 h hr.2
  · exact CubeGradient.slice_difference_le_variation hf hr.1 h hq.2

theorem dyadic_sample_total_influence {m : ℕ} {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) :
    (∑ i, scalarSampleInfluence (m:=m) f i) ≤ variation f := by
  induction m generalizing L f with
  | zero => simpa using variation_nonneg f
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    have hhead : scalarSampleInfluence (m:=m+1) f 0 ≤ variation f/2 := by
      apply (mean_mono (fun q => ?_)).trans_eq
        (show mean (fun _ : Cube (m+1) => variation f/2) = variation f/2 by simp [mean])
      have hc : Continuous (fun y => |(f (scalarCell q y) - f (scalarCell (flip 0 q) y))/2|) := by
        exact (((hf.continuous.comp (scalarCell_lipschitz q).continuous).sub
          (hf.continuous.comp (scalarCell_lipschitz (flip 0 q)).continuous)).div_const 2).abs
      have hh : (∫ y in (0:ℝ)..1, |(f (scalarCell q y)-f (scalarCell (flip 0 q) y))/2|) ≤
          ∫ _y in (0:ℝ)..1, variation f/2 := by
        apply intervalIntegral.integral_mono_on (by norm_num) (hc.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
        intro y hy
        rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
        exact div_le_div_of_nonneg_right (scalarCell_difference hf _ _ hy) (by norm_num)
      simpa using hh
    have ht : (∑ i : Fin m, scalarSampleInfluence (m:=m+1) f i.succ) =
        ((∑ i : Fin m, scalarSampleInfluence (m:=m) (f ∘ halfInput false) i) +
         (∑ i : Fin m, scalarSampleInfluence (m:=m) (f ∘ halfInput true) i))/2 := by
      simp only [scalarSampleInfluence_succ]
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    rw [ht]
    have h0 := ih (hf.comp (halfInput_lipschitz false))
    have h1 := ih (hf.comp (halfInput_lipschitz true))
    have hv := variation_half_sum hf
    linarith

end LargeIndependentSets.BooleanJunta

end OAI
