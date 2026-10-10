import OAI.NumberTheory.CubicMoment.Decomposition.StoppingLabelCollection
import OAI.NumberTheory.CubicMoment.Decomposition.StoppingFailedPair

namespace OAI

/-! Exact collection of both stages, including terms which never reach
the late threshold. The original support remains inside each pair sum. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem geometric_high_stopping_support_collection (S : Finset Eisenstein)
    {X : ℝ} (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (ρ Q : ℝ) (r : Eisenstein) (h : ℕ)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ S, geometricHighStoppedElement ρ X (norm r) Q h ψ w K n) =
      ∑ q ∈ (stoppingLabelBox ρ X).filter (fun q => q.1 < h),
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
          ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
            if d*e ∈ S then
              (if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                    q.1 q.2.1 h Q Q true r d ∧
                  stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
                cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (d*e) else 0)
            else 0 := by
  simpa only [geometricHighStoppedElement,stoppedSideTest,true_or,and_true] using
    geometric_stopping_label_collection S hS ρ Q r
      ((stoppingLabelBox ρ X).filter (fun q => q.1 < h)) ψ w K

theorem geometric_late_stopping_support_collection (S : Finset Eisenstein)
    {X : ℝ} (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    {ρ : ℝ} (hρ : 1 ≤ ρ) (r : Eisenstein) (h : ℕ)
    {Z Q : ℝ} (hQZ : Q ≤ Z)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ S with norm r*primeSurrogate
        (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q,
      geometricStoppedElement ρ X (norm r) Z ψ w K n) =
      ∑ q ∈ stoppingLabelBox ρ X, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
          if d*e ∈ S then
            (if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 h Z Q false r d ∧
                stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
              cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (d*e) else 0)
          else 0 := by
  let T := S.filter (fun n => norm r*primeSurrogate
    (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
    (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q)
  have hT : ∀ n ∈ T, primary n ∧ Squarefree n ∧ norm n ≤ X :=
    fun n hn => hS n (Finset.mem_filter.mp hn).1
  change (∑ n ∈ T, geometricStoppedElement ρ X (norm r) Z ψ w K n) = _
  simp_rw [geometricStoppedElement_eq_labels]
  rw [geometric_stopping_label_collection T hT ρ Z r (stoppingLabelBox ρ X) ψ w K]
  apply Finset.sum_congr rfl
  intro q _hq
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  by_cases hde : d*e ∈ S
  · simp only [T,Finset.mem_filter,hde,true_and,ite_true]
    by_cases hrem : stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e
    · rw [stoppedSideTest_failed_pair_iff (mem_primaryElementBall.mp hd).1
        (mem_primaryElementBall.mp he).1 (hS (d*e) hde).2.1
        (geometricPrimeBin ρ X) (geometricBinLower ρ X)
        (fun j => one_le_pow₀ hρ) q.1 q.2.1 q.2.2 h Z Q hQZ hrem]
      by_cases hstop : stoppingSideTest (geometricPrimeBin ρ X)
          (geometricBinLower ρ X) q.1 q.2.1 Z r d
      · simp only [hrem,hstop,true_and,and_true,ite_true]
      · simp only [hrem,hstop,false_and,and_true,ite_false,ite_self]
    · simp only [hrem,and_false,ite_false,ite_self]
  · simp only [T,Finset.mem_filter,hde,false_and,ite_false]

theorem finite_two_stage_stopping_pair_split (S : Finset Eisenstein)
    {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    {r : Eisenstein} (hr : primary r) {Q Z : ℝ}
    (hstart : norm r < Q) (hQZ : Q ≤ Z) (h : ℕ)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ S, cutoffMoebius ψ w n*K n) =
      (∑ n ∈ S with norm r*primeSurrogate
          (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q ∧
        norm r*primeSurrogate (primaryPrimeFactors n)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z,
        cutoffMoebius ψ w n*K n) +
      (∑ q ∈ (stoppingLabelBox ρ X).filter (fun q => q.1 < h),
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
          ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
            if d*e ∈ S then
              (if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                    q.1 q.2.1 h Q Q true r d ∧
                  stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
                cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (d*e) else 0)
            else 0) +
      ∑ q ∈ stoppingLabelBox ρ X, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
          if d*e ∈ S then
            (if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 h Z Q false r d ∧
                stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
              cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (d*e) else 0)
          else 0 := by
  rw [finite_two_stage_stopping_split S hρ hρ₂ hX hS (norm_pos_of_ne_zero (primary_ne_zero hr)) hstart hQZ h ψ w K,
    geometric_high_stopping_support_collection S hS ρ Q r h ψ w K,
    geometric_late_stopping_support_collection S hS hρ.le r h hQZ ψ w K]

end CubicFirstMoment

end

end OAI
