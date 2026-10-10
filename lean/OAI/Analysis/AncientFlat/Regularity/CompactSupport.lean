import Mathlib

namespace OAI
open scoped ContDiff NNReal
lemma hasCompactSupport_fderiv_bound {W E : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E] (f : W → E) (hf : ContDiff ℝ 1 f)
  (hs : HasCompactSupport f) : ∃ C : ℝ, ∀ p, ‖fderiv ℝ f p‖≤C := by
  exact (hs.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by norm_num))

end OAI
