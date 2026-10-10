import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroQuotientLog

namespace OAI

/-! # A local logarithmic-derivative expansion with its actual zero multiplicities -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem characterZeroPolynomial_logDeriv (χ : PrimitiveComplexCharacter) (S : Finset ℂ)
    (s : ℂ) (hs : s ∉ S) :
    logDeriv (characterZeroPolynomial χ S) s =
      ∑ z ∈ S, (analyticOrderNatAt χ.L z : ℂ) / (s - z) := by
  change logDeriv (fun w => ∏ z ∈ S, (w - z) ^ analyticOrderNatAt χ.L z) s = _
  rw [logDeriv_fun_prod]
  · apply Finset.sum_congr rfl
    intro z hz
    have hp := logDeriv_fun_pow (f := fun w : ℂ => w - z) (x := s)
      (differentiableAt_id.sub_const z) (analyticOrderNatAt χ.L z)
    rw [hp]
    simp [logDeriv_apply, div_eq_mul_inv]
  · intro z hz
    exact pow_ne_zero _ (sub_ne_zero.mpr (fun he => hs (he ▸ hz)))
  · intro z _
    exact (differentiableAt_id.sub_const z).pow _

/-- Away from the actual nearby zeros, L'/L differs from their partial fractions
by a controlled analytic term. No zero-separation assumption enters this term. -/
theorem character_logDeriv_local_error (χ : PrimitiveComplexCharacter) (t M : ℝ)
    (hM : 1 ≤ M)
    (hbound : ∀ z ∈ closedBall (characterZeroCenter t) (11 / 4 : ℝ), ‖χ.L z‖ ≤ M)
    (s : ℂ) (hs : ‖s - characterZeroCenter t‖ ≤ 5 / 2)
    (hszero : s ∉ characterContourZeros χ t) :
    ‖logDeriv χ.L s -
      ∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℂ) / (s - z)‖ ≤
      1312 * (Real.log (3 * M) +
        (∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℝ)) * Real.log 21 + 1) := by
  obtain ⟨g, hg, he, hgne⟩ := character_contour_quotient_exists χ t
  let c := characterZeroCenter t
  let A := Real.log (3 * M) +
    (∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℝ)) * Real.log 21 + 1
  have hA : 0 < A := by
    have hlog : 0 ≤ Real.log (3 * M) := Real.log_nonneg (by linarith)
    have h21 : 0 ≤ Real.log 21 := Real.log_nonneg (by norm_num)
    dsimp [A]
    positivity
  have hball (w : ℂ) (hw : w ∈ ball 0 (21 / 8 : ℝ)) :
      w + c ∈ closedBall c (21 / 8 : ℝ) := by
    simpa only [mem_closedBall, mem_ball, dist_zero_right, dist_eq_norm, add_sub_cancel_right, sub_zero]
      using (mem_ball_iff_norm.mp hw).le
  have hq := logDeriv_norm_le_contour_disk (fun w => g (w + c)) A hA
    (fun w _ => (hg (w + c)).comp (f := fun u : ℂ => u + c) (x := w) (by fun_prop))
    (fun w hw => hgne _ (hball w hw)) (fun w hw => ?_) (s - c) hs
  · have hsball : s ∈ closedBall c (21 / 8 : ℝ) := by
      rw [mem_closedBall, dist_eq_norm]
      linarith
    have hshift : logDeriv (fun w => g (w + c)) (s - c) = logDeriv g s := by
      change logDeriv (g ∘ (fun w => w + c)) (s - c) = _
      have hh := logDeriv_comp (f := g) (g := fun w : ℂ => w + c) (x := s - c)
        ((hg _).differentiableAt) (differentiableAt_id.add_const c)
      simpa using hh
    rw [hshift] at hq
    have hf : χ.L = fun w => characterZeroPolynomial χ (characterContourZeros χ t) w * g w :=
      funext he
    have hsplit : logDeriv χ.L s = logDeriv (characterZeroPolynomial χ (characterContourZeros χ t)) s + logDeriv g s := by
      rw [hf]
      exact logDeriv_fun_mul s
        (characterZeroPolynomial_ne_zero χ _ s hszero) (hgne s hsball)
        ((characterZeroPolynomial_analytic χ _ s).differentiableAt) ((hg s).differentiableAt)
    rw [hsplit, characterZeroPolynomial_logDeriv χ _ s hszero]
    simpa only [A, add_sub_cancel_left] using hq
  · have hh := character_contour_quotient_log_bound χ t M hM hbound g hg he hgne
      (w + c) (hball w hw)
    simpa only [zero_add, A, c] using hh.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))

end Ostmann

end OAI
