import OAI.NumberTheory.Ostmann.ZeroDensity.DensityHybridSieve

namespace OAI

/-! # The hybrid large sieve on translated height intervals -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Interval Classical

 theorem density_interval_translate_le (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) (T u : ℝ) (hT : 0 ≤ T) :
    (∫ t in Icc (-T) T, f (t + u)) ≤
      ∫ t in Icc (-(T + |u|)) (T + |u|), f t := by
  have he : (∫ t in Icc (-T) T, f (t + u)) =
      ∫ t in Icc (-T + u) (T + u), f t := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -T ≤ T),
      intervalIntegral.integral_comp_add_right, intervalIntegral.integral_of_le (by linarith : -T + u ≤ T + u),
      ← integral_Icc_eq_integral_Ioc]
  rw [he]
  apply setIntegral_mono_set hf.integrableOn_Icc (Filter.Eventually.of_forall hf0)
  apply Filter.Eventually.of_forall
  intro t ht
  exact ⟨by linarith [ht.1, neg_le_abs u], by linarith [ht.2, le_abs_self u]⟩

 theorem shifted_hybrid_multiplicative_large_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ N Q : ℕ, 1 ≤ Q → ∀ T u : ℝ, 1 ≤ T →
      ∀ a : ℕ → ℂ, ∀ F : (q : ℕ) → Finset (DirichletCharacter ℂ q),
      (∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ F q, χ.IsPrimitive) →
      (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ F q,
        ∫ t in Icc (-T) T, ‖∑ n ∈ Finset.Icc 1 N,
          a n * χ (n : ZMod q) * realAdditivePhase (-(Real.log n * (t + u)))‖ ^ 2) ≤
        C * ((N : ℝ) + (Q : ℝ) ^ 2 * (T + |u|)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := hybrid_multiplicative_large_sieve
  refine ⟨C, hC, ?_⟩
  intro N Q hQ T u hT a F hF
  apply le_trans _ (hb N Q hQ (T + |u|) (by linarith [abs_nonneg u]) a F hF)
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro χ hχ
  let f : ℝ → ℝ := fun t => ‖∑ n ∈ Finset.Icc 1 N,
    a n * χ (n : ZMod q) * realAdditivePhase (-(Real.log n * t))‖ ^ 2
  have hc : Continuous f := by
    dsimp [f, realAdditivePhase]
    fun_prop
  exact density_interval_translate_le f hc (fun t => sq_nonneg _) T u (by linarith)

end Ostmann

end OAI
