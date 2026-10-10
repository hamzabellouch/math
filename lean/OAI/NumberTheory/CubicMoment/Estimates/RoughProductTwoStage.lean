import OAI.NumberTheory.CubicMoment.Decomposition.StoppingSliceTwoStage
import OAI.NumberTheory.CubicMoment.Decomposition.StoppingMatrixLabels

namespace OAI

/-! The two-stage rough-product decomposition in independent coefficient
form. The distinguished coefficient is arbitrary and the original sharp
product support remains inside the kernel. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma sum_four_reorder_two_stage {α β γ δ : Type*}
    (A : Finset α) (B : Finset β) (C : Finset γ) (D : Finset δ)
    (F : α → β → γ → δ → ℂ) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, F a b c d) =
      ∑ d ∈ D, ∑ b ∈ B, ∑ a ∈ A, ∑ c ∈ C, F a b c d := by
  calc
    _ = ∑ a ∈ A, ∑ d ∈ D, ∑ b ∈ B, ∑ c ∈ C, F a b c d := by
      apply Finset.sum_congr rfl
      intro a _ha
      calc
        _ = ∑ b ∈ B, ∑ d ∈ D, ∑ c ∈ C, F a b c d := by
          apply Finset.sum_congr rfl
          intro b _hb
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, F a b c d := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _hd
      exact Finset.sum_comm

theorem rough_stopping_matrix_reindex (S R : Finset Eisenstein)
    (I : Finset (ℕ × ℕ × ℕ)) (ρ X Z Q : ℝ) (h : ℕ) (early : Bool)
    (v : Eisenstein → ℂ) (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ r ∈ R, v r * ∑ u ∈ primaryElementBall X,
      ∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ d ∈ primaryElementBall X, ∑ e ∈ primaryElementBall X,
          if r*(d*e)*u ∈ S then
            (if stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 h Z Q early r d ∧
                stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
              cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (r*(d*e)*u) else 0)
          else 0) =
      ∑ q ∈ I, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ a ∈ primaryPairSupport (primaryElementBall X) (primaryElementBall X),
          ∑ b ∈ primaryPairSupport R (primaryElementBall X),
            stoppedAlpha (primaryElementBall X) (primaryElementBall X) ψ w
                (stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2) a *
              stoppedBeta R (primaryElementBall X) v ψ w
                (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 h Z Q early) b *
              (if a*b ∈ S then K (a*b) else 0) := by
  conv_lhs =>
    arg 2
    ext r
    arg 2
    rw [Finset.sum_comm]
    simp only [←Finset.mul_sum]
  conv_lhs => simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [←stopping_matrix_collection_on_labels I ρ X Z Q h early R
    (primaryElementBall X) (primaryElementBall X) (primaryElementBall X)
    v ψ w (fun n => if n ∈ S then K n else 0)]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [sum_four_reorder_two_stage R (primaryElementBall X) (primaryElementBall X)
    (primaryElementBall X)]
  apply Finset.sum_congr rfl
  intro e _he
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro r _hr
  apply Finset.sum_congr rfl
  intro d _hd
  split_ifs <;> ring

theorem roughProduct_matrix_two_stage (S R : Finset Eisenstein)
    {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (hR : ∀ r ∈ R, primary r) {Q Z : ℝ}
    (v : Eisenstein → ℂ) (hstart : ∀ r ∈ R, v r ≠ 0 → norm r < Q) (hQZ : Q ≤ Z)
    (h : ℕ) (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ r ∈ R, v r *
      ∑ n ∈ primaryProductSlice S X r, (roughProduct ψ w n:ℂ)*K (r*n)) =
      (∑ r ∈ R, v r * ∑ u ∈ primaryElementBall X,
        ∑ m ∈ primaryProductSlice S X (r*u) with
          norm r*primeSurrogate
            (primeBinPrefix (primaryPrimeFactors m) (geometricPrimeBin ρ X) h)
            (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q ∧
          norm r*primeSurrogate (primaryPrimeFactors m)
            (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z,
          cutoffMoebius ψ w m*K (r*(m*u))) +
      (∑ q ∈ (stoppingLabelBox ρ X).filter (fun q => q.1 < h),
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
          ∑ a ∈ primaryPairSupport (primaryElementBall X) (primaryElementBall X),
            ∑ b ∈ primaryPairSupport R (primaryElementBall X),
              stoppedAlpha (primaryElementBall X) (primaryElementBall X) ψ w
                  (stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2) a *
                stoppedBeta R (primaryElementBall X) v ψ w
                  (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                    q.1 q.2.1 h Q Q true) b *
                (if a*b ∈ S then K (a*b) else 0)) +
      ∑ q ∈ stoppingLabelBox ρ X, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ a ∈ primaryPairSupport (primaryElementBall X) (primaryElementBall X),
          ∑ b ∈ primaryPairSupport R (primaryElementBall X),
            stoppedAlpha (primaryElementBall X) (primaryElementBall X) ψ w
                (stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2) a *
              stoppedBeta R (primaryElementBall X) v ψ w
                (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 h Z Q false) b *
              (if a*b ∈ S then K (a*b) else 0) := by
  simp_rw [roughProduct_slice_pairs S X hS]
  rw [←rough_stopping_matrix_reindex S R _ ρ X Q Q h true v ψ w K,
    ←rough_stopping_matrix_reindex S R _ ρ X Z Q h false v ψ w K]
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hv : v r = 0
  · simp only [hv,zero_mul,zero_add]
  rw [←mul_add,←mul_add]
  congr 1
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _hu
  exact stopping_product_slice_two_stage S hρ hρ₂ hX hS
    (hR r hr) u (hstart r hr hv) hQZ h ψ w K

end CubicFirstMoment

end

end OAI
