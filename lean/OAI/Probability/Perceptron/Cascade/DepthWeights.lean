import Mathlib
import OAI.Probability.Perceptron.Variational.DepthBlock

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology
namespace SphericalPerceptronFreeEnergy

lemma indexedDepthLaw_weight_tail (k : ℕ) (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (d : ℕ) :
    (indexedDepthLaw k (stepCumulative w) : Measure (FiniteOverlap (Fin (k+1)))).real
      {R | d ≤ (R 0 1).val} = ∑ i, if d ≤ i.val then w i else 0 := by
  by_cases hdk : d ≤ k
  · have hh := congrArg ENNReal.toReal (indexedDepthLaw_pair_tail k (stepCumulative w)
      (stepCumulative_strictMono w hw) (stepCumulative_pos w hw)
      (stepCumulative_lt_one w hw hw1) d hdk)
    have hb : (if h : d = 0 then (0:ℝ) else stepCumulative w ⟨d-1,by omega⟩) ≤ 1 := by
      split_ifs
      · norm_num
      · exact (stepCumulative_lt_one w hw hw1 _).le
    have he : (indexedDepthLaw k (stepCumulative w) : Measure (FiniteOverlap (Fin (k+1)))).real
        {R | d ≤ (R 0 1).val} =
        1 - (if h : d = 0 then 0 else stepCumulative w ⟨d-1,by omega⟩) := by
      simpa only [measureReal_def,ENNReal.toReal_ofReal (sub_nonneg.mpr hb)] using hh
    rw [he]
    by_cases hd0 : d = 0
    · subst d
      simpa only [dite_true,Nat.zero_le,ite_true,sub_zero] using hw1.symm
    · rw [dite_eq_right hd0,←hw1]
      unfold stepCumulative
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have hiff : i ≤ (⟨d-1,by omega⟩ : Fin k).castSucc ↔ ¬ d ≤ i.val := by
        change i.val ≤ d-1 ↔ ¬ d ≤ i.val
        omega
      by_cases hi : d ≤ i.val
      · simp only [ite_eq_left hi,ite_eq_right (fun h => (hiff.mp h) hi),sub_zero]
      · simp only [ite_eq_right hi,ite_eq_left (hiff.mpr hi),sub_self]
  · have hf (l : Fin (k+1)) : ¬ d ≤ l.val := by omega
    have he : {R : FiniteOverlap (Fin (k+1)) | d ≤ (R 0 1).val} = ∅ := by
      ext R
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      exact hf _
    rw [he]
    simp only [measureReal_empty,hf,ite_false,Finset.sum_const_zero]

theorem indexedDepthLaw_pair_weights (k : ℕ) (w : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (c : Fin (k+1)) :
    (indexedDepthLaw k (stepCumulative w) : Measure (FiniteOverlap (Fin (k+1)))).real
      {R | R 0 1 = c} = w c := by
  have h := measureReal_fin_atom_from_tails
    (indexedDepthLaw k (stepCumulative w) : Measure (FiniteOverlap (Fin (k+1))))
    k (fun R => R 0 1) (by fun_prop) univ MeasurableSet.univ c
  simp only [Set.mem_univ,true_and] at h
  rw [h,indexedDepthLaw_weight_tail k w hw hw1,indexedDepthLaw_weight_tail k w hw hw1,
    ←Finset.sum_sub_distrib]
  calc
    _ = ∑ i, if i = c then w c else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rcases lt_trichotomy i c with hi | rfl | hi
      · have h1 : ¬ c.val ≤ i.val := by exact not_le.mpr hi
        have h2 : ¬ c.val+1 ≤ i.val := by omega
        simp only [ite_eq_right h1,ite_eq_right h2,ite_eq_right (ne_of_lt hi),sub_self]
      · simp
      · have h1 : c.val ≤ i.val := le_of_lt hi
        have h2 : c.val+1 ≤ i.val := hi
        simp only [ite_eq_left h1,ite_eq_left h2,ite_eq_right (ne_of_gt hi),sub_self]
    _ = w c := by simp

end SphericalPerceptronFreeEnergy

end

end OAI
