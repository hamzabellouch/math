import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.HeightTemperedDistribution

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory

theorem tempered_distribution_finite_seminorm_bound {d : ℕ}
    (T : 𝓢'(Ambient d, ℂ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ g : 𝓢(Ambient d, ℂ),
        ‖T g‖ ≤ C * s.sup (schwartzSeminormFamily ℂ (Ambient d) ℂ) g := by
  let q : Seminorm ℂ 𝓢(Ambient d, ℂ) := (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hq : Continuous q := continuous_norm.comp T.continuous
  obtain ⟨s, C, hC, hbound⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℂ (Ambient d) ℂ) q hq
  refine ⟨s, C, by exact_mod_cast (pos_iff_ne_zero.mpr hC), fun g => ?_⟩
  exact hbound g

end

end RieszRectifiability

end OAI
