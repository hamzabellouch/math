import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDistinguishedIdentity
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSelectedBeta

namespace OAI

/-! Exact splitting of a valid largest-prime bin into its distinguished
and selected-divisor roles. The source stopping test is unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppedLargestBinTest (B ρ : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r d : Eisenstein) : Prop :=
  stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early r d ∧
    geometricPrimeBin ρ B (largestPrimeChoice (r*d)) = j

lemma largestPrimeChoice_prime_of_bin {B ρ : ℝ} {j : ℕ}
    (hj : j < geometricBinCount ρ B) {n : Eisenstein} (hn : primary n)
    (hbin : geometricPrimeBin ρ B (largestPrimeChoice n) = j) :
    primaryPrime (largestPrimeChoice n) ∧ largestPrimeChoice n ∣ n := by
  have hne : (primaryPrimeFactors n).Nonempty := by
    by_contra hempty
    have hchoice : largestPrimeChoice n = 1 := by
      simp only [largestPrimeChoice,dite_eq_right hempty]
    have hone : geometricPrimeBin ρ B (1 : Eisenstein) = geometricBinCount ρ B := by
      simp only [geometricPrimeBin,norm_one_eq,Real.log_one,zero_div,Nat.floor_zero,Nat.sub_zero]
    rw [hchoice,hone] at hbin
    omega
  exact primaryPrimeFactor_spec hn (largestPrimeChoice_spec hne).1

theorem stoppedBeta_largest_bin_roles (R D : Finset Eisenstein) (f : Eisenstein → ℂ)
    (w B ρ : ℝ) {j : ℕ} (hj : j < geometricBinCount ρ B)
    (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    {n : Eisenstein} (hn : primary n) (hs : Squarefree n) :
    stoppedBeta R D f primeDetectorCutoff w (stoppedLargestBinTest B ρ j j₀ k h Z Q early) n =
      stoppedBeta R D f primeDetectorCutoff w (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n+
      stoppedBeta R D f primeDetectorCutoff w (stoppedSelectedTest B ρ j j₀ k h Z Q early) n := by
  unfold stoppedBeta primaryPairCoefficient
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have he : t.1*t.2 = n := (Finset.mem_filter.mp ht).2
  by_cases htest : stoppedLargestBinTest B ρ j j₀ k h Z Q early t.1 t.2
  · obtain ⟨hstop,hbin⟩ := htest
    have hp := largestPrimeChoice_prime_of_bin hj hn (he ▸ hbin)
    have hsf : Squarefree (t.1*t.2) := he.symm ▸ hs
    have hdiv : largestPrimeChoice (t.1*t.2) ∣ t.1*t.2 := by simpa only [he] using hp.2
    have hp' : Prime (largestPrimeChoice (t.1*t.2)) := by simpa only [he] using hp.1.2
    rcases prime_factor_unique_side hp' hsf hdiv with ⟨hr,hnd⟩ | ⟨hd,hnr⟩
    · simp only [stoppedLargestBinTest,stoppedDistinguishedTest,stoppedSelectedTest,
        hstop,hbin,hr,hnd,and_self,and_false,and_true,ite_true,ite_false,add_zero]
    · simp only [stoppedLargestBinTest,stoppedDistinguishedTest,stoppedSelectedTest,
        hstop,hbin,hd,hnr,and_self,and_false,and_true,ite_true,ite_false,zero_add]
  · have hd : ¬stoppedDistinguishedTest B ρ j j₀ k h Z Q early t.1 t.2 := by
      rintro ⟨ha,_,hb⟩
      exact htest ⟨ha,hb⟩
    have hc : ¬stoppedSelectedTest B ρ j j₀ k h Z Q early t.1 t.2 := by
      rintro ⟨ha,_,hb⟩
      exact htest ⟨ha,hb⟩
    simp only [htest,hd,hc,ite_false,add_zero]

end CubicFirstMoment

end

end OAI
