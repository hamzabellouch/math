import OAI.Analysis.KadisonKastler.NormUltraproduct
import Mathlib.Analysis.Normed.Operator.NNNorm

namespace OAI

/-! # Bounded-sequence tests detect a uniform operator-norm limit

This is the diagonal choice in the infinitesimal normalizer argument:
equality of derivations on every element of the norm ultraproduct forces
their coordinate operator norms to tend to zero.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B C : ℕ → Type*} [∀ j, CStarAlgebra (B j)]
  [∀ j, CStarAlgebra (C j)]

theorem exists_unitBall_half_norm_witness (j : ℕ) (D : B j →L[ℂ] C j) :
    ∃ x : B j, ‖x‖ ≤ 1 ∧ ‖D‖ ≤ 2 * ‖D x‖ := by
  by_cases hD : ‖D‖ = 0
  · exact ⟨0, by simp, by simp [hD]⟩
  · have hp : 0 < ‖D‖ := (norm_nonneg D).lt_of_ne' hD
    obtain ⟨x, hx, hDx⟩ := D.exists_lt_apply_of_lt_opNorm (by linarith : ‖D‖ / 2 < ‖D‖)
    exact ⟨x, hx.le, by linarith⟩

theorem tendsto_opNorm_zero_of_bounded_sequence_tests (ω : Ultrafilter ℕ)
    (D : ∀ j, B j →L[ℂ] C j)
    (hD : ∀ x : VaryingBoundedSequence B,
      Tendsto (fun j => ‖D j (x j)‖) (ω : Filter ℕ) (𝓝 0)) :
    Tendsto (fun j => ‖D j‖) (ω : Filter ℕ) (𝓝 0) := by
  choose x hx hDx using fun j => exists_unitBall_half_norm_witness j (D j)
  let X : VaryingBoundedSequence B :=
    ⟨x, memℓp_infty ⟨1, by rintro _ ⟨j, rfl⟩; exact hx j⟩⟩
  apply squeeze_zero (fun j => norm_nonneg (D j)) hDx
  simpa only [mul_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) (ω : Filter ℕ) (𝓝 2)).mul (hD X)

end

end KadisonKastler

end OAI
