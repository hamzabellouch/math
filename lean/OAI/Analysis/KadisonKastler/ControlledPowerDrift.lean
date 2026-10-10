import OAI.Analysis.KadisonKastler.RandomizedRMS

namespace OAI

/-! # Adding the controlled lift to the positive word error -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {K Ω J : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] [Fintype Ω] [Nonempty Ω]

/-- Cancelling the test unitary separates the positive word error into
its word commutator and the controlled lift commutator. -/
theorem controlled_word_error_identity
    (T : K →L[ℂ] K) (Q s U : unitary (K →L[ℂ] K)) (ξ : K) :
    T (((Q : K →L[ℂ] K) * s * U) ξ) -
      ((Q : K →L[ℂ] K) * s * U) ((star (U : K →L[ℂ] K)) (T ((U : K →L[ℂ] K) ξ))) =
    (T * (Q : K →L[ℂ] K) - Q * T) ((s : K →L[ℂ] K) ((U : K →L[ℂ] K) ξ)) +
      (Q : K →L[ℂ] K) ((T * (s : K →L[ℂ] K) - s * T) ((U : K →L[ℂ] K) ξ)) := by
  have hc : (Q : K →L[ℂ] K) * s * U * star (U : K →L[ℂ] K) =
      (Q : K →L[ℂ] K) * s := by
    rw [mul_assoc ((Q : K →L[ℂ] K) * s), Unitary.mul_star_self_of_mem U.property, mul_one]
  have he : T * ((Q : K →L[ℂ] K) * s * U) -
      (Q : K →L[ℂ] K) * s * U * star (U : K →L[ℂ] K) * T * U =
      ((T * (Q : K →L[ℂ] K) - Q * T) * s + Q * (T * (s : K →L[ℂ] K) - s * T)) * U := by
    rw [hc]
    noncomm_ring
  simpa only [sub_apply, add_apply, mul_apply_eq_comp] using congrArg (fun a : K →L[ℂ] K => a ξ) he

/-- The controlled lift adds at most `2δ` to the word's root mean square. -/
theorem controlled_word_error_rms_le
    (T : K →L[ℂ] K) (Q : Ω → unitary (K →L[ℂ] K))
    (s U : unitary (K →L[ℂ] K)) (ξ : K) {δ : ℝ} (hδ : 0 ≤ δ)
    (hs : ‖T * (s : K →L[ℂ] K) - s * T‖ ≤ 2 * δ) :
    finiteRMS (fun θ => T (((Q θ : K →L[ℂ] K) * s * U) ξ) -
      ((Q θ : K →L[ℂ] K) * s * U)
        ((star (U : K →L[ℂ] K)) (T ((U : K →L[ℂ] K) ξ)))) ≤
    finiteRMS (fun θ => (T * (Q θ : K →L[ℂ] K) - Q θ * T)
      ((s : K →L[ℂ] K) ((U : K →L[ℂ] K) ξ))) + 2 * δ * ‖ξ‖ := by
  simp_rw [controlled_word_error_identity]
  apply (finiteRMS_add_le _ _).trans
  apply add_le_add le_rfl
  apply finiteRMS_le_const _ (by positivity)
  intro θ
  rw [Unitary.norm_map]
  calc
    _ ≤ ‖T * (s : K →L[ℂ] K) - s * T‖ * ‖(U : K →L[ℂ] K) ξ‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (2 * δ) * ‖(U : K →L[ℂ] K) ξ‖ :=
      mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ = _ := by rw [Unitary.norm_map]

/-- The `68δ` positive-word limit and the controlled lift give `70δ`. -/
theorem eventually_controlled_word_error
    (l : Filter J) (T : K →L[ℂ] K)
    (Q : J → Ω → unitary (K →L[ℂ] K))
    (s : J → unitary (K →L[ℂ] K)) (U : unitary (K →L[ℂ] K))
    (ξ : K) {δ : ℝ} (hδ : 0 ≤ δ)
    (hs : ∀ j, ‖T * (s j : K →L[ℂ] K) - s j * T‖ ≤ 2 * δ)
    (hword : ∀ ε > 0, ∀ᶠ j in l,
      finiteRMS (fun θ => (T * (Q j θ : K →L[ℂ] K) - Q j θ * T)
        ((s j : K →L[ℂ] K) ((U : K →L[ℂ] K) ξ))) ≤ 68 * δ * ‖ξ‖ + ε) :
    ∀ ε > 0, ∀ᶠ j in l,
      finiteRMS (fun θ => T (((Q j θ : K →L[ℂ] K) * s j * U) ξ) -
        ((Q j θ : K →L[ℂ] K) * s j * U)
          ((star (U : K →L[ℂ] K)) (T ((U : K →L[ℂ] K) ξ)))) ≤
            70 * δ * ‖ξ‖ + ε := by
  intro ε hε
  filter_upwards [hword ε hε] with j hj
  have ht := controlled_word_error_rms_le T (Q j) (s j) U ξ hδ (hs j)
  linarith

end

end KadisonKastler

end OAI
