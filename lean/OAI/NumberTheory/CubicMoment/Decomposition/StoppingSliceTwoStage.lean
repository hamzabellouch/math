import OAI.NumberTheory.CubicMoment.Decomposition.StoppingStageCollection
import OAI.NumberTheory.CubicMoment.Decomposition.StoppingProductSlice

namespace OAI

/-! Two-stage collection on the actual product slices. Multiplication
only changes the location of the original support predicate. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stopping_slice_pair_rows (S : Finset Eisenstein) (X : ℝ)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (r u : Eisenstein) (I : Finset (ℕ × ℕ × ℕ))
    (F : (ℕ × ℕ × ℕ) → Eisenstein → Eisenstein → ℂ) :
    (∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
      ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
        if d*e ∈ primaryProductSlice S X (r*u) then F q d e else 0) =
      ∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
          if r*(d*e)*u ∈ S then F q d e else 0 := by
  apply Finset.sum_congr rfl
  intro q _hq
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hm : primary (d*e) :=
    primary_mul (mem_primaryElementBall.mp hd).1 (mem_primaryElementBall.mp he).1
  have heq : (r*u)*(d*e) = r*(d*e)*u := by ring
  simp only [mem_primaryProductSlice_iff S X hS (r*u) hm,heq]

theorem stopping_product_slice_two_stage (S : Finset Eisenstein)
    {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    {r : Eisenstein} (hr : primary r) (u : Eisenstein) {Q Z : ℝ}
    (hstart : norm r < Q) (hQZ : Q ≤ Z) (h : ℕ)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ m ∈ primaryProductSlice S X (r*u), cutoffMoebius ψ w m*K (r*(m*u))) =
      (∑ m ∈ primaryProductSlice S X (r*u) with
          norm r*primeSurrogate
            (primeBinPrefix (primaryPrimeFactors m) (geometricPrimeBin ρ X) h)
            (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q ∧
          norm r*primeSurrogate (primaryPrimeFactors m)
            (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z,
        cutoffMoebius ψ w m*K (r*(m*u))) +
      (∑ q ∈ (stoppingLabelBox ρ X).filter (fun q => q.1 < h),
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
          ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
            if r*(d*e)*u ∈ S then
              (if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                    q.1 q.2.1 h Q Q true r d ∧
                  stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
                cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (r*(d*e)*u) else 0)
            else 0) +
      ∑ q ∈ stoppingLabelBox ρ X, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
          if r*(d*e)*u ∈ S then
            (if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 h Z Q false r d ∧
                stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
              cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (r*(d*e)*u) else 0)
          else 0 := by
  rw [finite_two_stage_stopping_pair_split (primaryProductSlice S X (r*u))
    hρ hρ₂ hX (primaryProductSlice_support S X hS (r*u)) hr hstart hQZ h ψ w
    (fun m => K (r*(m*u)))]
  have hrows (I : Finset (ℕ × ℕ × ℕ)) (T : ℝ) (early : Bool) :
      (∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
          if d*e ∈ primaryProductSlice S X (r*u) then
            (if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 h T Q early r d ∧
                stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
              cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (r*((d*e)*u)) else 0)
          else 0) =
        ∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
          ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
            if r*(d*e)*u ∈ S then
              (if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                    q.1 q.2.1 h T Q early r d ∧
                  stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
                cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (r*(d*e)*u) else 0)
            else 0 := by
    simpa only [mul_assoc] using stopping_slice_pair_rows S X hS r u I
      (fun q d e => if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
          q.1 q.2.1 h T Q early r d ∧
        stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
          cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (r*((d*e)*u)) else 0)
  rw [hrows,hrows]

end CubicFirstMoment

end

end OAI
