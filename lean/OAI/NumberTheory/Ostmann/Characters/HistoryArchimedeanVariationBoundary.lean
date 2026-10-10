import Mathlib.Algebra.BigOperators.Intervals
import OAI.NumberTheory.Ostmann.Characters.OneSidedBilinearProgressions

namespace OAI

noncomputable section
namespace Ostmann.Characters
open scoped BigOperators

def intervalRestrictedWeight (a b : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if a ≤ n ∧ n ≤ b then f n else 0

private theorem sum_indicator_le {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (P : ι → Prop) [DecidablePred P] {M : ℝ} (hM : 0 ≤ M)
    (hunique : ∀ i ∈ S, ∀ j ∈ S, P i → P j → i=j) :
    (∑ i ∈ S, if P i then M else 0) ≤ M := by
  rw [← Finset.sum_filter]
  have hc : (S.filter P).card ≤ 1 := Finset.card_le_one.mpr (by
    intro i hi j hj
    exact hunique i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)
  have hcr : ((S.filter P).card : ℝ) ≤ 1 := by exact_mod_cast hc
  simpa only [Finset.sum_const,nsmul_eq_mul,one_mul] using
    mul_le_mul_of_nonneg_right hcr hM

theorem progressionVariation_interval_restriction_le (a b N : ℕ) (f : ℕ → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ n, a ≤ n → n ≤ b → ‖f n‖ ≤ M) :
    progressionVariation (intervalRestrictedWeight a b f) N ≤
      3*M+(∑ n ∈ Finset.Ico a b, ‖f (n+1)-f n‖) := by
  classical
  have hnorm (n : ℕ) : ‖intervalRestrictedWeight a b f n‖ ≤ M := by
    unfold intervalRestrictedWeight
    split_ifs with hn
    · exact hf n hn.1 hn.2
    · simpa only [norm_zero] using hM
  have hstep (n : ℕ) :
      ‖intervalRestrictedWeight a b f (n+1)-intervalRestrictedWeight a b f n‖ ≤
        (if n+1=a then M else 0)+(if n=b then M else 0)+
          (if n ∈ Finset.Ico a b then ‖f (n+1)-f n‖ else 0) := by
    by_cases hnext : a ≤ n+1 ∧ n+1 ≤ b
    · by_cases hcurr : a ≤ n ∧ n ≤ b
      · have hi : n ∈ Finset.Ico a b := Finset.mem_Ico.mpr ⟨hcurr.1,by omega⟩
        simp only [intervalRestrictedWeight,ite_eq_left hnext,ite_eq_left hcurr,ite_eq_left hi]
        have h1 : 0 ≤ if n+1=a then M else 0 := by split_ifs <;> positivity
        have h2 : 0 ≤ if n=b then M else 0 := by split_ifs <;> positivity
        linarith
      · have he : n+1=a := by omega
        simp only [intervalRestrictedWeight,ite_eq_left hnext,ite_eq_right hcurr,sub_zero,ite_eq_left he]
        have h1 : 0 ≤ if n=b then M else 0 := by split_ifs <;> positivity
        have h2 : 0 ≤ if n ∈ Finset.Ico a b then ‖f (n+1)-f n‖ else 0 := by split_ifs <;> positivity
        linarith [hf (n+1) hnext.1 hnext.2]
    · by_cases hcurr : a ≤ n ∧ n ≤ b
      · have he : n=b := by omega
        simp only [intervalRestrictedWeight,ite_eq_right hnext,ite_eq_left hcurr,zero_sub,norm_neg,ite_eq_left he]
        have h1 : 0 ≤ if n+1=a then M else 0 := by split_ifs <;> positivity
        have h2 : 0 ≤ if n ∈ Finset.Ico a b then ‖f (n+1)-f n‖ else 0 := by split_ifs <;> positivity
        linarith [hf n hcurr.1 hcurr.2]
      · simp only [intervalRestrictedWeight,ite_eq_right hnext,ite_eq_right hcurr,sub_self,norm_zero]
        positivity
  have hentry := sum_indicator_le (Finset.range (N-1)) (fun n : ℕ => n+1=a) hM
    (fun i _ j _ hi hj => by omega)
  have hexit := sum_indicator_le (Finset.range (N-1)) (fun n : ℕ => n=b) hM
    (fun i _ j _ hi hj => by omega)
  have hinterior : (∑ n ∈ Finset.range (N-1),
      if n ∈ Finset.Ico a b then ‖f (n+1)-f n‖ else 0) ≤
        ∑ n ∈ Finset.Ico a b, ‖f (n+1)-f n‖ := by
    rw [← Finset.sum_filter]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun n hn => (Finset.mem_filter.mp hn).2) (fun n _ _ => norm_nonneg _)
  have hsum := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range (N-1)) => hstep n)
  simp only [Finset.sum_add_distrib] at hsum
  unfold progressionVariation
  linarith [hnorm (N-1)]

end Ostmann.Characters

end

end OAI
