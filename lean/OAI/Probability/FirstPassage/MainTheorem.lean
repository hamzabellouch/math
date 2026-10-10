import OAI.Probability.FirstPassage.UnitSphereC1

namespace OAI

namespace PlanarFPP

theorem fullMainDifferentiability : FullMainDifferentiabilityTarget := by
  intro Ω _ P τ henv
  exact ⟨actualSourceTimeConstant,actualSourceTimeConstant_norm,
    actualSourceTimeConstant_isTimeConstant henv,actual_differentiable_away henv,
    unique_supports_of_differentiable _ actualSourceTimeConstant_norm (actual_differentiable_away henv),
    actual_C1_unit_sphere henv⟩

theorem mainDifferentiability : MainDifferentiabilityTarget := by
  intro Ω _ P τ μ henv _hμ ht
  have he := actualSourceTimeConstant_unique henv ht
  subst μ
  exact ⟨actual_differentiable_away henv,
    unique_supports_of_differentiable _ actualSourceTimeConstant_norm (actual_differentiable_away henv),
    actual_C1_unit_sphere henv⟩

end PlanarFPP

end OAI
