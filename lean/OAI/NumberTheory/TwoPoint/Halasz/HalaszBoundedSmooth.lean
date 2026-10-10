import OAI.NumberTheory.TwoPoint.Halasz.HalaszTriplePrefix

namespace OAI

/-! The smooth-series step needs only a bounded coefficient. In particular
it applies to the actual typical coefficient, whose value at one may vanish. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_bounded_smooth_summable (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) (t : ℝ) :
    LSeriesSummable (halaszSmoothFunction f N) (1+(t:ℂ)*Complex.I) := by
  have hs := halasz_smooth_LSeries_summable (fun _ => (1:ℂ)) rfl
    (by intros; simp) (by intro n hn; simp) N t
  apply hs.norm.of_norm_bounded
  intro n
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  by_cases hsm : n ∈ Nat.smoothNumbers (N+1)
  · simp only [LSeries.term, hn, ite_false, halaszSmoothFunction, hsm, ite_true,
      norm_div, norm_one]
    exact div_le_div_of_nonneg_right (hf n (Nat.pos_of_ne_zero hn)) (norm_nonneg _)
  · simp [LSeries.term, hn, halaszSmoothFunction, hsm]

end TwoPointCorrelations

end OAI
