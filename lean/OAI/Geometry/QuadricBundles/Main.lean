import OAI.Geometry.QuadricBundles.Ampleness

namespace OAI

noncomputable section

namespace QuadricCounterexample
noncomputable section

theorem main_theorem : SourceMainTheorem := by
  let G := sourceGraphScalars.equalizerData.bundle
  let E : ℕ → AlgebraicRankTwoBundle := fun m ↦
    if hm : 0 < m then powerPullbackTwist G m hm else G
  refine ⟨G,E,?_,?_,?_⟩
  · intro m hm
    dsimp [E]
    rw [dite_eq_left hm]
    exact powerPullbackTwist_spec G m hm
  · intro m hm
    dsimp [E]
    rw [dite_eq_left hm]
    exact sourceGraphScalars.equalizerData.powerTwist_ample m hm
  · obtain ⟨m₀,h₀,h⟩ := source_eventually_no_positive_metric
    refine ⟨m₀,h₀,fun m hmi ↦ ?_⟩
    have hm : 0 < m := h₀.trans_le hmi
    dsimp [E]
    rw [dite_eq_left hm]
    exact h m hm hmi

end
end QuadricCounterexample

end

end OAI
