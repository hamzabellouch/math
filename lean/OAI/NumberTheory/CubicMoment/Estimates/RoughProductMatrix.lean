import OAI.NumberTheory.CubicMoment.Decomposition.StoppingProductSlice
import OAI.NumberTheory.CubicMoment.Decomposition.StoppingMatrixCollection

namespace OAI

/-! The actual rough-product divisor expansion collected into the
independent stopping coefficients. Original finite support and kernel are
retained, and the no-stop summand is not discarded. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma sum_four_reorder {α β γ δ : Type*}
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

/-- Every distinguished row of the original rough-product expansion
equals its literal no-stop term plus the independent stopped matrix.
The inverse binomial is unchanged; total support is carried inside K. -/
theorem roughProduct_matrix_stopping (S R : Finset Eisenstein)
    {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (hR : ∀ r ∈ R, primary r) {Z : ℝ} (hstart : ∀ r ∈ R, norm r < Z)
    (h : ℕ) (Q : ℝ) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ r ∈ R, v r *
      ∑ n ∈ primaryProductSlice S X r, (roughProduct ψ w n:ℂ)*K (r*n)) =
      (∑ r ∈ R, v r *
        ∑ u ∈ primaryElementBall X,
          ∑ m ∈ primaryProductSlice S X (r*u) with
            norm r*primeSurrogate (primaryPrimeFactors m)
              (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z,
            cutoffMoebius ψ w m*K (r*(m*u))) +
      ∑ q ∈ stoppingLabelBox ρ X, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
        ∑ a ∈ primaryPairSupport (primaryElementBall X) (primaryElementBall X),
          ∑ b ∈ primaryPairSupport R (primaryElementBall X),
            stoppedAlpha (primaryElementBall X) (primaryElementBall X) ψ w
                (stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2) a *
              stoppedBeta R (primaryElementBall X) v ψ w
                (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                  q.1 q.2.1 h Z Q true) b *
              (if a*b ∈ S then K (a*b) else 0) := by
  calc
    _ = (∑ r ∈ R, v r *
        ∑ u ∈ primaryElementBall X,
          ∑ m ∈ primaryProductSlice S X (r*u) with
            norm r*primeSurrogate (primaryPrimeFactors m)
              (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z,
            cutoffMoebius ψ w m*K (r*(m*u))) +
        ∑ r ∈ R, v r *
          ∑ q ∈ stoppingLabelBox ρ X, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
            ∑ u ∈ primaryElementBall X, ∑ d ∈ primaryElementBall X,
              ∑ e ∈ primaryElementBall X,
                if r*(d*e)*u ∈ S then
                  (if stoppingSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
                        q.1 q.2.1 Z r d ∧
                      stoppingRemainingTest (geometricPrimeBin ρ X) q.1 q.2.2 e then
                    cutoffMoebius ψ w d*cutoffMoebius ψ w e*K (r*(d*e)*u) else 0)
                else 0 := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      rw [←mul_add,roughProduct_slice_stopping S hρ hρ₂ hX hS
        (hR r hr) (hstart r hr) ψ w K]
    _ = _ := by
      congr 1
      conv_lhs => simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      rw [←stopping_matrix_collection ρ X Z Q h true R
        (primaryElementBall X) (primaryElementBall X) (primaryElementBall X)
        v ψ w (fun n => if n ∈ S then K n else 0)]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      rw [sum_four_reorder R (primaryElementBall X) (primaryElementBall X)
        (primaryElementBall X)]
      apply Finset.sum_congr rfl
      intro e _he
      apply Finset.sum_congr rfl
      intro u _hu
      apply Finset.sum_congr rfl
      intro r _hr
      apply Finset.sum_congr rfl
      intro d _hd
      have hside : stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
          q.1 q.2.1 h Z Q true r d ↔
          stoppingSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
            q.1 q.2.1 Z r d := by simp [stoppedSideTest]
      simp only [hside]
      split_ifs <;> ring

end CubicFirstMoment

end

end OAI
