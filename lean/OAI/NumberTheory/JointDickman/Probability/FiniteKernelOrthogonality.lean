import OAI.NumberTheory.JointDickman.Amplification.FiniteAdditiveOrthogonality

namespace OAI

/-! # Exact Fourier representation of the finite equation a-b=jc -/

namespace JointDickman
open Finset MeasureTheory

theorem integral_additive_triple (a b c j : ℕ) (u v w : ℂ) :
    (∫ θ in (0 : ℝ)..1,
      (u*additivePhase ((a : ℝ)*θ)) * (v*additivePhase ((b : ℝ)*(-θ))) *
        (w*additivePhase ((c : ℝ)*(-(j : ℝ)*θ)))) =
      if a = b+j*c then u*v*w else 0 := by
  have he : (fun θ : ℝ =>
      (u*additivePhase ((a : ℝ)*θ)) * (v*additivePhase ((b : ℝ)*(-θ))) *
        (w*additivePhase ((c : ℝ)*(-(j : ℝ)*θ)))) =
      (fun θ : ℝ => (u*v*w)*additivePhase (((a : ℤ)-b-(j : ℤ)*c : ℤ)*θ)) := by
    funext θ
    have hp : additivePhase (((a : ℤ)-b-(j : ℤ)*c : ℤ)*θ) =
        additivePhase ((a : ℝ)*θ)*additivePhase ((b : ℝ)*(-θ))*
          additivePhase ((c : ℝ)*(-(j : ℝ)*θ)) := by
      rw [← additivePhase_add,← additivePhase_add]
      congr 1
      push_cast
      ring
    rw [hp]
    ring
  rw [he,intervalIntegral.integral_const_mul,integral_additivePhase_int]
  have hz : (a : ℤ)-b-(j : ℤ)*c = 0 ↔ a = b+j*c := by
    rw [← Int.natCast_mul]
    omega
  by_cases h : a = b+j*c
  · simp [h]
  · simp [h,mt hz.mp h]

/-- The finite sum and integral are identical, before any arc is discarded. -/
theorem finiteKernel_orthogonality (A B C : Finset ℕ) (u v w : ℕ → ℂ) (j : ℕ) :
    (∫ θ in (0 : ℝ)..1,
      finiteAdditiveSum A u θ * finiteAdditiveSum B v (-θ) *
        finiteAdditiveSum C w (-(j : ℝ)*θ)) =
      ∑ c ∈ C, ∑ b ∈ B, ∑ a ∈ A, if a = b+j*c then u a*v b*w c else 0 := by
  have hc (a b c : ℕ) : Continuous (fun θ : ℝ =>
      (u a*additivePhase ((a : ℝ)*θ))*(v b*additivePhase ((b : ℝ)*(-θ)))*
        (w c*additivePhase ((c : ℝ)*(-(j : ℝ)*θ)))) := by
    apply Continuous.mul
    · apply Continuous.mul
      · exact continuous_const.mul (continuous_additivePhase.comp (continuous_const.mul continuous_id))
      · exact continuous_const.mul (continuous_additivePhase.comp (continuous_const.mul continuous_neg))
    · exact continuous_const.mul (continuous_additivePhase.comp
        (continuous_const.mul (continuous_const.mul continuous_id)))
  simp only [finiteAdditiveSum,mul_sum,sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro c _
    rw [intervalIntegral.integral_finsetSum]
    · apply sum_congr rfl
      intro b _
      rw [intervalIntegral.integral_finsetSum]
      · apply sum_congr rfl
        intro a _
        exact integral_additive_triple a b c j (u a) (v b) (w c)
      · intro a _
        exact (hc a b c).intervalIntegrable 0 1
    · intro b _
      apply Continuous.intervalIntegrable
      apply continuous_finsetSum
      intro a _
      exact hc a b c
  · intro c _
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro b _
    apply continuous_finsetSum
    intro a _
    exact hc a b c

end JointDickman

end OAI
