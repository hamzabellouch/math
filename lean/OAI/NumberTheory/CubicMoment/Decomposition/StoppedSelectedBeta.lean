import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSelectedMoment

namespace OAI

/-! Selected-side prime cancellation applies to the literal
stoppedBeta coefficient, with its global-largest role selected exactly. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppedSelectedTest (B ρ : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ) (early : Bool)
    (r d : Eisenstein) : Prop :=
  stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B) j₀ k h Z Q early r d ∧
    largestPrimeChoice (r*d) ∣ d ∧ geometricPrimeBin ρ B (largestPrimeChoice (r*d)) = j

lemma selected_largest_bin_nonempty {B ρ : ℝ} {j : ℕ}
    (hj : j < geometricBinCount ρ B) {r d : Eisenstein} (hr : primary r) (hd : primary d)
    (hrole : largestPrimeChoice (r*d) ∣ d)
    (hbin : geometricPrimeBin ρ B (largestPrimeChoice (r*d)) = j) :
    (primaryPrimeFactors d).Nonempty := by
  have hne : (primaryPrimeFactors (r*d)).Nonempty := by
    by_contra hempty
    have hc : largestPrimeChoice (r*d) = 1 := by
      simp only [largestPrimeChoice,dite_eq_right hempty]
    rw [hc] at hbin
    have hone : geometricPrimeBin ρ B (1 : Eisenstein) = geometricBinCount ρ B := by
      simp only [geometricPrimeBin,norm_one_eq,Real.log_one,zero_div,Nat.floor_zero,Nat.sub_zero]
    rw [hone] at hbin
    omega
  have hp := (primaryPrimeFactor_spec (primary_mul hr hd) (largestPrimeChoice_spec hne).1).1
  exact ⟨largestPrimeChoice (r*d),(primaryPrime_mem_factors_iff hd).mpr ⟨hp,hrole⟩⟩

lemma selectedStoppedDivisorSet_eq {B ρ a b : ℝ} {j j₀ k h : ℕ}
    (hj : j < geometricBinCount ρ B) (Z Q : ℝ) (early : Bool) (r e : Eisenstein)
    (hr : primary r) :
    selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e =
      (primaryElementBall B).filter (fun d =>
        (Squarefree (r*d) ∧ IsCoprime (r*d) e ∧ a < norm (r*d) ∧ norm (r*d) ≤ b) ∧
          stoppedSelectedTest B ρ j j₀ k h Z Q early r d) := by
  ext d
  constructor
  · intro hmem
    obtain ⟨hd,hs,_hne,hcop,hint,hrole,hbin,hstop⟩ := Finset.mem_filter.mp hmem
    exact Finset.mem_filter.mpr ⟨hd,⟨hs,hcop,hint.1,hint.2⟩,hstop,hrole,hbin⟩
  · intro hmem
    obtain ⟨hd,⟨hs,hcop,ha,hb⟩,hstop,hrole,hbin⟩ := Finset.mem_filter.mp hmem
    exact Finset.mem_filter.mpr
      ⟨hd,hs,selected_largest_bin_nonempty hj hr (mem_primaryElementBall.mp hd).1 hrole hbin,
        hcop,⟨ha,hb⟩,hrole,hbin,hstop⟩

/-- Exact coefficient collection; all analytic cancellation belongs to
`stopped_selected_original_saving`, already proved from the raw input. -/
theorem stoppedBeta_selected_identity {B ρ a b w u : ℝ} {j j₀ k h : ℕ}
    (hj : j < geometricBinCount ρ B) (Z Q : ℝ) (early : Bool)
    (R : Finset Eisenstein) (hR : ∀ r ∈ R, primary r)
    (f : Eisenstein → ℂ) (v e : Eisenstein) :
    (∑ n ∈ primaryPairSupport R (primaryElementBall B),
      stoppedBeta R (primaryElementBall B) f primeDetectorCutoff w
        (stoppedSelectedTest B ρ j j₀ k h Z Q early) n *
      (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
        then normTwist u n*cubicSymbol n v else 0)) =
      ∑ r ∈ R, f r*∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
        cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*cubicSymbol (r*d) v := by
  unfold stoppedBeta
  rw [primaryPairCoefficient_sum,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro r hr
  rw [selectedStoppedDivisorSet_eq hj Z Q early r e (hR r hr),Finset.mul_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases ht : stoppedSelectedTest B ρ j j₀ k h Z Q early r d
  · by_cases hc : Squarefree (r*d) ∧ IsCoprime (r*d) e ∧ a < norm (r*d) ∧ norm (r*d) ≤ b
    · simp only [ht,hc,and_self,ite_true]
      ring
    · simp only [ht,hc,false_and,ite_false,mul_zero]
  · simp only [ht,and_false,ite_false,zero_mul]

end CubicFirstMoment

end

end OAI
