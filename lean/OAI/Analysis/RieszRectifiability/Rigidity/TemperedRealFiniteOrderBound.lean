import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.TemperedFiniteOrderBound

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap

theorem tempered_distribution_finite_real_seminorm_bound {d : ℕ}
    (T : 𝓢'(Ambient d, ℂ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ g : 𝓢(Ambient d, ℂ),
        ‖T g‖ ≤ C * s.sup (schwartzSeminormFamily ℝ (Ambient d) ℂ) g := by
  obtain ⟨s, C, hC, hbound⟩ := tempered_distribution_finite_seminorm_bound T
  refine ⟨s, C, hC, fun g => ?_⟩
  have heq : s.sup (schwartzSeminormFamily ℂ (Ambient d) ℂ) g =
      s.sup (schwartzSeminormFamily ℝ (Ambient d) ℂ) g := by
    simp only [Seminorm.finset_sup_apply]
    rfl
  exact (hbound g).trans_eq (congrArg (fun t : ℝ => C * t) heq)

end

end RieszRectifiability

end OAI
